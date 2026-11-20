module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.FpCommon
@[expose] public section

/-! Floating-point comparison prerequisites for data-to-word assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

open Flapjack

/-- Every HOL one-bit word is zero or one. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word1_cases"]
theorem word1Cases (w : BitVec 1) : w = 0 ∨ w = 1 := by bv_decide

/-- Comparison symmetry on finite rational values, used by the local HOL theorem. -/
private theorem ratGreaterSwap (a b : Rat) :
    ((if a < b then HolFloatCompare.lt else if a = b then .eq else .gt) == .gt) =
      ((if b < a then HolFloatCompare.lt else if b = a then .eq else .gt) == .lt) ∧
    (match (if a < b then HolFloatCompare.lt else if a = b then .eq else .gt) with
      | .gt | .eq => true | _ => false) =
    (match (if b < a then HolFloatCompare.lt else if b = a then .eq else .gt) with
      | .lt | .eq => true | _ => false) := by
  rcases lt_trichotomy a b with h | h | h
  · have hba : ¬ b < a := not_lt_of_ge (le_of_lt h)
    have hab : a ≠ b := ne_of_lt h
    have hbaEq : b ≠ a := Ne.symm hab
    simp [h, hba, hbaEq]
  · subst b
    simp
  · have hab : ¬ a < b := not_lt_of_ge (le_of_lt h)
    have hne : b ≠ a := ne_of_lt h
    have hne2 : a ≠ b := Ne.symm hne
    simp [h, hab, hne2]

/-- Comparison symmetry for the shared float model; this is proof infrastructure for `fp_greater`. -/
private theorem floatGreaterSwap {t w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) :
    holFloatGreaterThan x y = holFloatLessThan y x ∧
      holFloatGreaterEqual x y = holFloatLessEqual y x := by
  have sx := word1Cases x.sign
  have sy := word1Cases y.sign
  rcases sx with sx | sx <;> rcases sy with sy | sy <;>
    cases hx : holFloatValue x <;> cases hy : holFloatValue y <;>
    simp [holFloatGreaterThan, holFloatLessThan, holFloatGreaterEqual, holFloatLessEqual,
      holFloatCompare, hx, hy, sx, sy, ratGreaterSwap]
  all_goals exact (ratGreaterSwap _ _).2

/-- Greater FP comparisons equal less comparisons with the operands reversed. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "fp_greater"
  (reals_as_rational_cuts)]
theorem fpGreater (a b : BitVec 64) :
    holFp64GreaterThan a b = holFp64LessThan b a ∧
      holFp64GreaterEqual a b = holFp64LessEqual b a := by
  simpa [holFp64GreaterThan, holFp64LessThan, holFp64GreaterEqual, holFp64LessEqual] using
    floatGreaterSwap (holFp64ToFloat a) (holFp64ToFloat b)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
