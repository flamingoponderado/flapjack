import Flapjack.Pancake.WordLang

namespace Flapjack

/-- Flapjack-only correspondence for the legacy positive-width immediate
predicate. There is no independent HOL theorem for equality of these two Lean
representations; the zero-width legacy interface remains outside this result. -/
theorem everyVarImmHOL_eq_everyVarImm {width : Nat} [NeZero width]
    (predicate : Nat → Bool) (operand : WordRegImm (BitVec width)) :
    everyVarImmHOL predicate operand = everyVarImm predicate operand := by
  cases operand <;> rfl

/-- Flapjack-only exact-to-legacy instruction predicate correspondence. This
retains all constructors, including the six selected memory operations and the
width-64 FP move branch. It assumes no evaluation or target equality.

Caller audit: non-test uses of the legacy predicates are in `everyVar`, a
proposition-valued program recursor. This theorem does not claim that an executed
compiler route invokes either predicate or that the full program carrier matches
HOL (its cutset representation remains a separate gap). -/
theorem everyVarInstHOL_eq_everyVarInst {width : Nat} [NeZero width]
    (predicate : Nat → Bool) (instruction : WordLangInst (BitVec width)) :
    everyVarInstHOL predicate instruction = everyVarInst predicate instruction := by
  cases instruction with
  | arith operation =>
      cases operation <;>
        simp only [everyVarInstHOL, everyVarInst, everyVarImmHOL_eq_everyVarImm]
  | mem operation destination address =>
      cases operation <;> cases address <;> rfl
  | _ => rfl

/-- Flapjack-only consumer boundary: the existing proposition-valued recursor's
instruction case is equivalent to checking the reviewed positive-width predicate.
No assertion about the other program cases or compiler routing is made. -/
theorem everyVar_inst_iff_exact {width : Nat} [NeZero width]
    (predicate : Nat → Bool) (instruction : WordLangInst (BitVec width)) :
    everyVar predicate (.inst instruction) ↔ everyVarInstHOL predicate instruction = true := by
  rw [everyVarInstHOL_eq_everyVarInst]
  rfl

end Flapjack
