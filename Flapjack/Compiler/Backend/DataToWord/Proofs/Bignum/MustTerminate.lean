module

public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
public import Flapjack.Misc.GoodDimindex
public import Mathlib.Tactic

@[expose] public section

/-! Bounds on the word-semantics `MustTerminate` clock used by the bignum proofs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack

private theorem twoLe_dimword (width : Nat) [NeZero width] : 2 ≤ 2 ^ width := by
  have := Nat.pos_of_ne_zero (NeZero.ne width)
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ width := Nat.pow_le_pow_right (by omega) this

private theorem twoDimword_le_limit (width : Nat) [NeZero width] :
    2 * 2 ^ width ≤ wordSemMustTerminateLimit width := by
  simp only [wordSemMustTerminateLimit]
  omega

/-- At a good width, the termination limit dominates a quadratic in the word modulus. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "MustTerminate_limit_eq"
  (word_dimension_as_width := width)]
theorem mustTerminateLimit_eq (width : Nat) [NeZero width] :
    goodDimindex width →
      ∃ k, wordSemMustTerminateLimit width = 10 * 2 ^ width * 2 ^ width + 10 * 2 ^ width + 100 + k := by
  intro good
  have big : 16 ≤ 2 ^ width := by rcases good with h | h <;> subst h <;> norm_num
  have bound : 10 * 2 ^ width * 2 ^ width + 10 * 2 ^ width + 100 ≤ wordSemMustTerminateLimit width := by
    simp only [wordSemMustTerminateLimit]
    generalize hd : (2 : Nat) ^ width = d at *
    have cube : d ^ 3 ≤ d ^ d := Nat.pow_le_pow_right (by omega) (by omega)
    have small : 10 * d * d + 10 * d + 100 ≤ d ^ 3 := by
      have dd := Nat.mul_le_mul_right d big
      have ddd := Nat.mul_le_mul_right d dd
      rw [show d ^ 3 = d * d * d by ring]
      nlinarith
    omega
  exact ⟨_, (Nat.add_sub_cancel' bound).symm⟩

/-- At a good width, the termination limit minus two is at least the word modulus. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "MustTerminate_limit_SUB_2"
  (word_dimension_as_width := width)]
theorem mustTerminateLimit_sub_2 (width : Nat) [NeZero width] :
    goodDimindex width → 2 ^ width ≤ wordSemMustTerminateLimit width - 2 := by
  intro _
  have := twoLe_dimword width
  have := twoDimword_le_limit width
  omega

/-- Values below the word modulus are below the termination limit minus one. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "IMP_LESS_MustTerminate_limit"
  (word_dimension_as_width := width)]
theorem imp_less_mustTerminateLimit (width : Nat) [NeZero width] (i : Nat) :
    i < 2 ^ width → i < wordSemMustTerminateLimit width - 1 := by
  intro h
  have := twoLe_dimword width
  have := twoDimword_le_limit width
  omega

/-- The termination limit exceeds two. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "TWO_LESS_MustTerminate_limit"
  (word_dimension_as_width := width)]
theorem two_less_mustTerminateLimit (width : Nat) [NeZero width] :
    2 < wordSemMustTerminateLimit width ∧ ¬ wordSemMustTerminateLimit width ≤ 1 := by
  have := twoLe_dimword width
  have := twoDimword_le_limit width
  omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
