module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AdjustedSet
public import Flapjack.Compiler.Backend.Semantics.WordSem.State
public import Flapjack.Compiler.Backend.BackendProps
public import Flapjack.HolRef

@[expose] public section

/-! Supporting lemmas of the data-to-word division assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps

/-- Shifting a word right by one less than its width leaves its sign bit. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_bit_lsr_dimindex_1"
  (words_as_type_indexed_bitvec)]
theorem wordBit_lsr_dimindex_1 {width : Nat} [NeZero width] (w1 : BitVec width) :
    (w1 >>> (width - 1)).getLsbD 0 = true ↔ w1.msb = true := by
  have pos := NeZero.pos width
  rw [BitVec.getLsbD_ushiftRight, Nat.add_zero, BitVec.msb_eq_getLsbD_last]

/-- The bound on an optional sum is independent of the summand order. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "option_le_add_comm"]
theorem optionLe_add_comm (a b c : Option Nat) :
    optionLe (wordSemOptionAdd a b) c → optionLe (wordSemOptionAdd b a) c := by
  cases a <;> cases b <;> cases c <;> simp [wordSemOptionAdd, optionLe]; omega

/-- Every adjusted live name recovers a source live name. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "IN_adjust_set_IN"]
theorem in_adjustSet_in {α : Type} (y : Nat) (x : Spt α) :
    sptDomain (adjustSet x) y → sptDomain x ((y - 2) / 2) := by
  intro member
  obtain ⟨n, rfl, present⟩ := (Proofs.Gc.adjustSet_domain x y).mp member
  have : (adjustVar n - 2) / 2 = n := by simp only [adjustVar]; omega
  rw [this]
  exact present

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
