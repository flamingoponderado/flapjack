import Flapjack.Compiler.Backend.BviTailrec.Proofs.RewriteCorrespondence

/-! Relationships between scan results and tail-rewrite flags. The source
carriers remain subject to HOL review. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

/-- An operation scan selects its recognized accumulator exactly when its
candidate check succeeds. -/
theorem scanSing_op_choice (ctx : List ValueType) (loc : Nat) (actual : ClosLang.Op) (args : List Exp) :
    (scanSing ctx loc (.op actual args)).2.2.2 =
      if fromOp actual == .noop then none
      else if (checkOp ctx (fromOp actual) loc (.op actual args)).isSome then some (fromOp actual)
      else none := by
  rw [scanSing.eq_def]
  dsimp only
  split
  · split
    · split <;> split <;> rfl
    · split <;> rfl
  · split
    · rfl
    · split
      · split <;> rfl
      · rfl

/-- For an operation, the rewrite flag reflects whether the scan selected the
requested accumulator, provided the accumulator is not `noop`. -/
theorem rewriteSingle_op_scan (ctx : List ValueType) (loc next acc : Nat)
    (assoc : AssocOp) (actual : ClosLang.Op) (args : List Exp) (notNoop : assoc ≠ .noop) :
    ((scanSing ctx loc (.op actual args)).2.2.2 = none →
      (rewriteSingle loc next assoc acc ctx (.op actual args)).1 = false) ∧
    ((scanSing ctx loc (.op actual args)).2.2.2 = some assoc →
      (rewriteSingle loc next assoc acc ctx (.op actual args)).1 = true) := by
  rw [scanSing_op_choice, rewriteSingle.eq_def]
  dsimp only
  by_cases same : fromOp actual = assoc
  · have notRecognized : (fromOp actual == .noop) = false := by
      rw [same]
      cases assoc <;> simp_all [BEq.beq, instBEqAssocOp.beq, AssocOp.ctorIdx]
    have guard : (fromOp actual == assoc && assoc != .noop) = true := by
      rw [same]
      cases assoc <;> simp_all [BEq.beq, instBEqAssocOp.beq, AssocOp.ctorIdx, bne]
    rw [notRecognized, guard]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [same]
    cases checked : checkOp ctx assoc loc (.op actual args) with
    | none => simp
    | some checkedExp =>
      obtain ⟨value, ticks, dest, callArgs, shape⟩ :=
        checkOp_success_shape ctx assoc loc _ checkedExp checked
      subst checkedExp
      simp [applyOp]
  · have guard : (fromOp actual == assoc && assoc != .noop) = false := by
      cases h : fromOp actual <;> cases assoc <;>
        simp_all [BEq.beq, instBEqAssocOp.beq, AssocOp.ctorIdx, bne]
    rw [guard]
    simp only [Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro _; trivial
    · intro scan
      split at scan
      · simp at scan
      · split at scan
        · simp at scan
          exact (same scan).elim
        · simp at scan

/-- The rewrite flag agrees with the scan's operator choice. This is
untagged until the evaluator-independent carriers are source-reviewed. -/
theorem rewriteSingle_scan (e : Exp) (ctx : List ValueType) (loc next acc : Nat)
    (assoc : AssocOp) (notNoop : assoc ≠ .noop) :
    ((scanSing ctx loc e).2.2.2 = none → (rewriteSingle loc next assoc acc ctx e).1 = false) ∧
    ((scanSing ctx loc e).2.2.2 = some assoc → (rewriteSingle loc next assoc acc ctx e).1 = true) := by
  cases e with
  | var n => simp [scanSing.eq_def, rewriteSingle.eq_def]
  | force location index => simp [scanSing.eq_def, rewriteSingle.eq_def]
  | tick body =>
    have ih := rewriteSingle_scan body ctx loc next acc assoc notNoop
    rw [scanSing.eq_def, rewriteSingle.eq_def]
    dsimp only
    cases scan : scanSing ctx loc body with
    | mk first rest =>
      cases rewritten : rewriteSingle loc next assoc acc ctx body with
      | mk flag out => simpa [scan, rewritten] using ih
  | «let» bindings body =>
    let scans := scanList ctx loc bindings
    let types := scans.map fun (_, ty, _, _) => ty
    let last := match scans.getLast? with | some (cs, _, _, _) => cs | none => ctx
    have ih := rewriteSingle_scan body (types ++ last) loc next (acc + bindings.length) assoc notNoop
    rw [scanSing.eq_def, rewriteSingle.eq_def]
    dsimp only
    cases scan : scanSing (types ++ last) loc body with
    | mk first rest =>
      cases rewritten : rewriteSingle loc next assoc (acc + bindings.length) (types ++ last) body with
      | mk flag out => simpa [scan, rewritten] using ih
  | ifThenElse cond yes no =>
    let context := (scanSing ctx loc cond).1
    have iy := rewriteSingle_scan yes context loc next acc assoc notNoop
    have ineg := rewriteSingle_scan no context loc next acc assoc notNoop
    rw [scanSing.eq_def, rewriteSingle.eq_def]
    dsimp only
    cases hy : scanSing context loc yes with
    | mk cy ry =>
      rcases ry with ⟨ty, byFlag, opy⟩
      cases hn : scanSing context loc no with
      | mk cn rn =>
        rcases rn with ⟨tn, bnFlag, opn⟩
        cases wy : rewriteSingle loc next assoc acc context yes with
        | mk flagy outy =>
          cases wn : rewriteSingle loc next assoc acc context no with
          | mk flagn outn =>
            simp only [hy, wy] at iy
            simp only [hn, wn] at ineg
            cases opy <;> cases opn <;> cases flagy <;> cases flagn <;> simp_all
  | op actual args => exact rewriteSingle_op_scan ctx loc next acc assoc actual args notNoop
  | raise body => simp [scanSing.eq_def, rewriteSingle.eq_def]
  | «return» args => simp [scanSing.eq_def, rewriteSingle.eq_def]
  | call ticks dest args handler => simp [scanSing.eq_def, rewriteSingle.eq_def]
  | letCall rets ticks dest args body => simp [scanSing.eq_def, rewriteSingle.eq_def]
termination_by sizeOf e

/-- Source-shaped rewrite/scan invariant: no scan choice means no rewrite;
a matching selected operator forces the rewrite flag. The scan and rewrite
carriers remain subject to source review. -/
theorem rewrite_scan_expr (loc next : Nat) (assoc : AssocOp) (acc : Nat)
    (ctx : List ValueType) (e : Exp) (outCtx : List ValueType) (ty : ValueType)
    (flag : Bool) (output : Exp) (branch : Bool) (choice : Option AssocOp)
    (rewritten : rewriteSource loc next assoc acc ctx e = (flag, output))
    (notNoop : assoc ≠ .noop)
    (scanned : scanExpr ctx loc [e] = [(outCtx, ty, branch, choice)]) :
    match choice with
    | none => flag = false
    | some selected => assoc = selected → flag = true := by
  have invariant := rewriteSingle_scan e ctx loc next acc assoc notNoop
  rw [rewriteSingle_eq_source, rewritten] at invariant
  have selected : (scanSing ctx loc e).2.2.2 = choice := by
    rw [scanExpr_single] at scanned
    have eq : scanSing ctx loc e = (outCtx, ty, branch, choice) := by simpa using scanned
    rw [eq]
  cases choice with
  | none => exact invariant.1 selected
  | some op =>
    intro same
    subst op
    exact invariant.2 selected

end Flapjack.Compiler.Backend.BviTailrec
