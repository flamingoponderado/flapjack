import Flapjack.Compiler.Backend.WordCse.Proofs.EvaluationFrames
import Flapjack.Misc.SptreeLookup

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack Compiler.Encoders.Asm WordSemStateFiniteExact AssignmentResults LoadEvaluationSupport

/-! Full original register-deletion frames used by StoreConsts. Untagged value
factoring has no separate HOL declaration; it agrees with actual native `inst`.
These statements require neither local-map well-formedness nor destination
separation. The inherited evaluator rational-cut assumption remains item 8. -/

private def arithValue {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (s : WordSemStateFiniteExact width C F) : Option (WordLocW width) :=
  match a with
  | .binop op _ src ri =>
    wordExp s (.op op [.var src, match ri with | .reg r => .var r | .imm w => .const w])
  | .shift sh _ src ri =>
    wordExp s (.shift sh (.var src) (match ri with | .reg r => .var r | .imm w => .const w))
  | .div _ src1 src2 =>
    match WordSemStateFiniteExact.getVars [src2, src1] s with
    | some [.word q, .word v] => if q ≠ 0 then some (.word (v.sdiv q)) else none
    | _ => none
  | _ => none

private theorem instArithMap {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (s : WordSemStateFiniteExact width C F) (h : canMemArith a = true) :
    inst (.arith (HolArith.toWordLangArith a)) s =
      (arithValue a s).map (fun v => setVar (firstRegOfArith a) v s) := by
  cases a with
  | binop op dst src ri =>
    cases ri <;> simp [HolArith.toWordLangArith, HolRegImm.toWordRegImm, inst, arithValue,
      firstRegOfArith, assignMap]
  | shift sh dst src ri =>
    cases ri <;> simp [HolArith.toWordLangArith, HolRegImm.toWordRegImm, inst, arithValue,
      firstRegOfArith, assignMap]
  | div dst src1 src2 =>
    simp only [HolArith.toWordLangArith, inst, arithValue, firstRegOfArith]
    split <;> simp_all [Option.map]
    split <;> simp_all
  | _ => simp [canMemArith] at h

private theorem lookupDeleteOther {α : Type} (t : Spt α) (n k : Nat) (h : n ≠ k) :
    sptLookup k (sptDelete n t) = sptLookup k t := by
  simp [sptLookup_sptDelete, Ne.symm h]

private theorem arithValueUnsetVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (r : Nat) (s : WordSemStateFiniteExact width C F)
    (h : r ∉ arithReads a) : arithValue a (unsetVar r s) = arithValue a s := by
  cases a with
  | binop op dst src ri =>
    cases ri <;> simp_all [arithValue, arithReads, wordExp, getVar, unsetVar,
      lookupDeleteOther]
  | shift sh dst src ri =>
    cases ri <;> simp_all [arithValue, arithReads, wordExp, getVar, unsetVar,
      lookupDeleteOther]
  | div dst src1 src2 =>
    simp_all [arithValue, arithReads, WordSemStateFiniteExact.getVars, getVar, unsetVar,
      lookupDeleteOther]
  | _ => rfl

private theorem loadValueUnsetVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (a n : Nat) (ofs : BitVec width)
    (s : WordSemStateFiniteExact width C F) (h : a ≠ n) :
    loadValue op a ofs (unsetVar n s) = loadValue op a ofs s := by
  cases op <;> simp [loadValue, wordExp, getVar, unsetVar, sptLookup_sptDelete, h, memLoad]
  all_goals rfl

namespace DeletionFramesWitness

theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end DeletionFramesWitness

/-- Full original arithmetic deletion equivalence under exactly eligibility and
absence from the arithmetic read list. Deleted register may be the destination. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateArithUnsetVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (r : Nat) (w : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (h : canMemArith a = true ∧ r ∉ arithReads a) :
    (evaluate (.inst (.arith (HolArith.toWordLangArith a))) (unsetVar r s) =
      (none, setVar (firstRegOfArith a) w (unsetVar r s))) ↔
    evaluate (.inst (.arith (HolArith.toWordLangArith a))) s =
      (none, setVar (firstRegOfArith a) w s) := by
  rw [evaluationAssignmentIff _ _ (arithValue a (unsetVar r s)) (unsetVar r s) w
    (instArithMap a (unsetVar r s) h.1)]
  rw [evaluationAssignmentIff _ _ (arithValue a s) s w (instArithMap a s h.1)]
  rw [arithValueUnsetVar a r s h.2]

/-- Full original load deletion equivalence. Only the original non-store and
address-register distinction guards constrain the operation and deletion. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateLoadUnsetVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (r a : Nat) (ofs : BitVec width) (n : Nat) (w : WordLocW width)
    (s : WordSemStateFiniteExact width C F) (h : isStore op = false ∧ a ≠ n) :
    (evaluate (.inst (.mem op r (.addr a ofs))) (unsetVar n s) =
      (none, setVar r w (unsetVar n s))) ↔
    evaluate (.inst (.mem op r (.addr a ofs))) s = (none, setVar r w s) := by
  rw [evaluationAssignmentIff _ r (loadValue op a ofs (unsetVar n s)) (unsetVar n s) w
    (instLoadMap op r a ofs (unsetVar n s) h.1)]
  rw [evaluationAssignmentIff _ r (loadValue op a ofs s) s w (instLoadMap op r a ofs s h.1)]
  rw [loadValueUnsetVar op a n ofs s h.2]

end Flapjack.Compiler.Backend.WordCse
