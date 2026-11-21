module

public import Flapjack.HolRef
public import Mathlib.Data.Int.Basic

@[expose] public section

/-! Integer facts used by the data-to-word assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

/-- A nonnegative integer is the integer embedding of a natural number. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "INT_EQ_NUM_LEMMA"]
theorem int_eq_nat_iff (i : Int) : 0 ≤ i ↔ ∃ index : Nat, i = Int.ofNat index := by
  constructor
  · intro h
    exact ⟨i.toNat, (Int.toNat_of_nonneg h).symm⟩
  · rintro ⟨index, rfl⟩
    exact Int.natCast_nonneg index

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
