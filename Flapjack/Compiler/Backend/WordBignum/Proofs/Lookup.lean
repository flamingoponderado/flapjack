import Flapjack.Compiler.Backend.WordBignum.Compile
import Flapjack.Compiler.Backend.WordBignum.Proofs.Equality

/-! The executable code cache compares the complete syntax, including nested
expressions. This is a Flapjack infrastructure fact, not a HOL theorem port. -/
namespace Flapjack.Compiler.Backend.WordBignum

/-- Proof-side first-match lookup using the checked decidable equality. -/
def lookupCodeByEquality {width : Nat} (code : Mini (BitVec width)) :
    List (CodeEntry width) → Option Nat
  | [] => none
  | (body, index, _) :: rest => if code = body then some index else lookupCodeByEquality code rest

/-- Cache lookup implements first-match propositional equality. -/
theorem lookupCode_eq_byEquality {width : Nat} (code : Mini (BitVec width))
    (entries : List (CodeEntry width)) : lookupCode code entries = lookupCodeByEquality code entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨body, index, result⟩ := entry
    by_cases h : code = body
    · subst code
      have eq := (miniEq_iff body body).mpr rfl
      simp [lookupCode, lookupCodeByEquality, eq]
    · have ne : miniEq code body = false := by
        cases he : miniEq code body with
        | false => rfl
        | true => exact False.elim (h ((miniEq_iff code body).mp he))
      simp [lookupCode, lookupCodeByEquality, ne, h, ih]

end Flapjack.Compiler.Backend.WordBignum
