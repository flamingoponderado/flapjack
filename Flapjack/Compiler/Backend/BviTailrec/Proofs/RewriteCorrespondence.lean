import Flapjack.Compiler.Backend.BviTailrec.Proofs.ScanCorrespondence
import Flapjack.Compiler.Backend.BviTailrec.Proofs.Total

/-! Fuel-free normal form for the executed accumulator rewrite. Connecting its
operation case to the complete HOL rewrite definition is a separate step. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

/-- Flapjack's fuel-free rewrite, with source-shaped scans and candidate checks.
The operation dispatch is the executable's normalized form. -/
def rewriteSingle (loc next : Nat) (op : AssocOp) (acc : Nat)
    (ctx : List ValueType) : Exp → Bool × Exp
  | .var n => (false, .var n)
  | .force l n => (false, .force l n)
  | .ifThenElse cond yes no =>
    let ctx' := (scanSing ctx loc cond).1
    let (ry, y) := rewriteSingle loc next op acc ctx' yes
    let (rn, n) := rewriteSingle loc next op acc ctx' no
    let y := if ry then y else applyOp op (.var acc) yes
    let n := if rn then n else applyOp op (.var acc) no
    (ry || rn, .ifThenElse cond y n)
  | .let xs body =>
    let scans := scanList ctx loc xs
    let types := scans.map fun (_, ty, _, _) => ty
    let last := match scans.getLast? with | some (cs, _, _, _) => cs | none => ctx
    let (r, body) := rewriteSingle loc next op (acc + xs.length) (types ++ last) body
    (r, .let xs body)
  | .tick x =>
    let (r, x) := rewriteSingle loc next op acc ctx x
    (r, .tick x)
  | .op actual xs =>
    if fromOp actual == op && op != .noop then
      match checkOp ctx op loc (.op actual xs) with
      | some (.op _ [value, .call ticks (some _) args handler]) =>
        (true, .call ticks (some next) (args ++ [applyOp op (.var acc) value]) handler)
      | _ => (false, applyOp op (.var acc) (.op actual xs))
    else (false, applyOp op (.var acc) (.op actual xs))
  | e => (false, applyOp op (.var acc) e)
termination_by e => sizeOf e

/-- An operation rewrite uses the same candidate check as the fuel-free form. -/
theorem rewriteFuel_op_eq (fuel loc next : Nat) (op : AssocOp) (acc : Nat)
    (ctx : List ValueType) (actual : ClosLang.Op) (xs : List Exp) :
    rewriteFuel (fuel + 1) loc next op acc ctx (.op actual xs) =
      some (rewriteSingle loc next op acc ctx (.op actual xs)) := by
  rw [rewriteFuel, rewriteSingle.eq_def]
  cases op <;> cases hop : fromOp actual <;>
    simp_all [BEq.beq, instBEqAssocOp.beq, AssocOp.ctorIdx, bne]
  all_goals
    have recognized : fromOp actual ≠ .noop := by rw [hop]; decide
    have checked := checkOpFuel_eq_recognized fuel ctx actual loc xs recognized
    simp only [hop] at checked
    rw [checked]
    simp only [Option.bind]
    split <;> simp_all

/-- Any successful bounded rewrite equals the fuel-free normal form. -/
theorem rewriteFuel_eq (fuel loc next : Nat) (op : AssocOp) (acc : Nat)
    (ctx : List ValueType) (e : Exp) (result : Bool × Exp)
    (run : rewriteFuel fuel loc next op acc ctx e = some result) :
    result = rewriteSingle loc next op acc ctx e := by
  induction fuel generalizing acc ctx e result with
  | zero => simp [rewriteFuel] at run
  | succ fuel ih =>
    cases e with
    | op actual xs =>
      rw [rewriteFuel_op_eq] at run
      exact (Option.some.inj run).symm
    | ifThenElse cond yes no =>
      cases hy : rewriteFuel fuel loc next op acc (scanSing ctx loc cond).1 yes with
      | none => simp [rewriteFuel, scanBounded_eq, hy] at run
      | some y =>
        have yeq := ih acc _ yes y hy
        subst y
        cases hn : rewriteFuel fuel loc next op acc (scanSing ctx loc cond).1 no with
        | none => simp [rewriteFuel, scanBounded_eq, hy, hn] at run
        | some n =>
          have neq := ih acc _ no n hn
          subst n
          rw [rewriteSingle.eq_def]
          simpa [rewriteFuel, scanBounded_eq, hy, hn] using run.symm
    | «let» xs body =>
      simp only [rewriteFuel, scanListBounded_eq, bind, Option.bind, pure] at run
      generalize hb : rewriteFuel fuel loc next op (acc + xs.length) _ body = answer at run
      cases answer with
      | none => simp at run
      | some b =>
        have beq := ih (acc + xs.length) _ body b hb
        subst b
        rw [rewriteSingle.eq_def]
        cases last : (scanList ctx loc xs).getLast? with
        | none => simpa only [last, Option.bind, Option.some.injEq] using run.symm
        | some s =>
          obtain ⟨a, b, c, d⟩ := s
          simpa only [last, Option.bind, Option.some.injEq] using run.symm
    | tick body =>
      cases hb : rewriteFuel fuel loc next op acc ctx body with
      | none => simp [rewriteFuel, hb] at run
      | some b =>
        have beq := ih acc ctx body b hb
        subst b
        rw [rewriteSingle.eq_def]
        simpa [rewriteFuel, hb] using run.symm
    | var n => simpa [rewriteFuel, rewriteSingle.eq_def] using run.symm
    | force l n => simpa [rewriteFuel, rewriteSingle.eq_def] using run.symm
    | raise e => simpa [rewriteFuel, rewriteSingle.eq_def] using run.symm
    | call a b c d => simpa [rewriteFuel, rewriteSingle.eq_def] using run.symm
    | «return» xs => simpa [rewriteFuel, rewriteSingle.eq_def] using run.symm
    | letCall a b c d e => simpa [rewriteFuel, rewriteSingle.eq_def] using run.symm

/-- Flapjack's fuel-free expression compilation normal form. -/
def compileExpSingle (loc next arity : Nat) (e : Exp) : Option (Exp × Exp) :=
  match checkExpSingle loc arity e with
  | none => none
  | some op =>
    let worker := (rewriteSingle loc next op arity (List.replicate arity .any) e).2
    let wrapper := .let ((List.range arity).map .var ++ [identity op]) worker
    some (wrapper, worker)

/-- A successful expression compilation equals the fuel-free normal form. -/
theorem compileExpFuel_eq (fuel loc next arity : Nat) (e : Exp)
    (result : Option (Exp × Exp)) (run : compileExpFuel fuel loc next arity e = some result) :
    result = compileExpSingle loc next arity e := by
  cases decision : checkExpSingle loc arity e with
  | none => simpa [compileExpFuel, compileExpSingle, checkExpFuel_eq, decision] using run.symm
  | some op =>
    cases rewrite : rewriteFuel fuel loc next op arity (List.replicate arity .any) e with
    | none => simp [compileExpFuel, checkExpFuel_eq, decision, rewrite] at run
    | some output =>
      have eq := rewriteFuel_eq fuel loc next op arity (List.replicate arity .any) e output rewrite
      subst output
      simpa [compileExpFuel, compileExpSingle, checkExpFuel_eq, decision, rewrite] using run.symm

/-- The production retry returns the fuel-free expression compilation result. -/
theorem compileExpBounded_eq (fuel loc next arity : Nat) (e : Exp) :
    compileExpBounded fuel loc next arity e = some (compileExpSingle loc next arity e) := by
  cases first : compileExpFuel fuel loc next arity e with
  | some result =>
    have eq := compileExpFuel_eq fuel loc next arity e result first
    subst result
    simp [compileExpBounded, first]
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := compileExpFuel_succeeds (max fuel (expBudget e + 1)) loc next arity e bound
    have eq := compileExpFuel_eq _ loc next arity e result done
    subst result
    simp [compileExpBounded, first, done]

end Flapjack.Compiler.Backend.BviTailrec
