import Flapjack.Pancake.WordLang

namespace Flapjack

/-- Pointwise predicate implication preserves the original instruction-variable
predicate. All native instruction constructors and the width-64 FP-transfer
clauses are retained; no register-bound or evaluation premise is added. -/
-- riscv-mi: integer-only specialization of the referenced HOL declaration.

theorem everyVarInstMono {width : Nat} [NeZero width]
    (P : Nat → Bool) (instruction : WordLangInst (BitVec width)) (Q : Nat → Bool) :
    (∀ x, P x = true → Q x = true) ∧ everyVarInstHOL P instruction = true →
      everyVarInstHOL Q instruction = true := by
  rintro ⟨hPQ, hP⟩
  have immMono (immediate : WordRegImm (BitVec width)) :
      everyVarImmHOL P immediate = true → everyVarImmHOL Q immediate = true := by
    cases immediate <;> simp_all [everyVarImmHOL]
  cases instruction with
  | skip => rfl
  | const destination value => exact hPQ destination hP
  | arith operation =>
    cases operation <;> simp_all [everyVarInstHOL, Bool.and_eq_true]
  | mem operation destination address =>
    cases address
    cases operation <;> simp_all [everyVarInstHOL, Bool.and_eq_true]

end Flapjack
