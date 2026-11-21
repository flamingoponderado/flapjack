module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Sub

@[expose] public section

/-! Supporting lemmas of the data-to-word multiplication assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

/-- Cutting a state keeps its FFI state. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_state_opt_IMP_ffi"]
theorem cutStateOpt_ffi {C F : Type} (namesOpt : Option NumSet) (s x : DataSem.State C F) :
    DataSem.cutStateOpt namesOpt s = some x → x.ffi = s.ffi := by
  cases namesOpt with
  | none => intro h; cases h; rfl
  | some names =>
    intro h
    simp only [DataSem.cutStateOpt, DataSem.cutState, Option.map_eq_some_iff] at h
    obtain ⟨env, _, rfl⟩ := h
    rfl

/-- Halving four times a number doubles it. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "quad_times_div_half_double"]
theorem quadTimesDivHalfDouble (j : Nat) : 4 * j / 2 = 2 * j := by
  omega

/-- The product of two word values is below the square of the word modulus. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "w2n_mul_less"
  (words_as_type_indexed_bitvec)]
theorem w2n_mul_less {width : Nat} [NeZero width] :
    ∀ w w' : BitVec width, w.toNat * w'.toNat < (2 ^ width) ^ 2 := by
  intro w w'
  rw [Nat.pow_two]
  exact Nat.mul_lt_mul'' w.isLt w'.isLt

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
