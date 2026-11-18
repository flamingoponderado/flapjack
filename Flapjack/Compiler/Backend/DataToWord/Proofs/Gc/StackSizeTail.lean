module

public import Flapjack.Compiler.Backend.BackendProps
public import Flapjack.Compiler.Backend.Semantics.WordSem.State
public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
public import Flapjack.Misc.GoodDimindex
public import Mathlib.Tactic

@[expose] public section

/-! Stack accounting for the data-to-word pop-environment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.BackendProps

/-- Incrementing a word wraps exactly when it has the largest unsigned value. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "w2n_minus_1_LESS_EQ"
  (words_as_type_indexed_bitvec)]
theorem wordMaxLeIffAddOneEqZero {width : Nat} [NeZero width] (w : BitVec width) :
    (-1 : BitVec width).toNat ≤ w.toNat ↔ w + 1 = 0 := by
  have hp : 1 < 2 ^ width := by
    simp [NeZero.ne width]
  have hw := w.isLt
  change (-(BitVec.ofNat width 1)).toNat ≤ w.toNat ↔ w + BitVec.ofNat width 1 = BitVec.ofNat width 0
  simp only [BitVec.toNat_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp,
    BitVec.toNat_add, BitVec.toNat_eq, Nat.zero_mod]
  rw [Nat.mod_eq_of_lt (by omega : 2 ^ width - 1 < 2 ^ width)]
  by_cases h : w.toNat + 1 < 2 ^ width
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have hmax : w.toNat + 1 = 2 ^ width := by omega
    rw [hmax, Nat.mod_self]
    omega

/-- A byte-aligned word plus one cannot be zero at a supported word width. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "bytes_in_word_ADD_1_NOT_ZERO"
  (words_as_type_indexed_bitvec)]
theorem bytesInWordAddOneNeZero {width : Nat} [NeZero width] (w : BitVec width)
    (good : goodDimindex width) : wordSemBytesInWord * w + 1 ≠ 0 := by
  rcases good with h | h <;> subst width <;> simp only [wordSemBytesInWord] <;> bv_decide

/-- Taking a maximum with the bound preserves the other operand's comparison. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "option_le_OPTION_MAP2_MAX"]
theorem optionLeOptionMap2Max (n m : Option Nat) :
    (optionLe (Option.map₂ max n m) n ↔ optionLe m n) ∧
    (optionLe (Option.map₂ max m n) n ↔ optionLe m n) := by
  simp [optionLe_max, optionLe_refl]

/-- Removing the top frame preserves its saved local-size bound. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "option_le_tl"
  (words_as_type_indexed_bitvec)]
theorem optionLe_tail {width : Nat} [NeZero width]
    (opt : Option Nat) (ws vs : List (Nat × WordLocW width))
    (handler : Option (Nat × Nat × Nat)) (ys : List (WordSemStackFrame width))
    (s t : Option Nat)
    (bound : optionLe (wordSemOptionAdd
      (wordSemStackSize (.stackFrame opt ws vs handler :: ys)) s) t) :
    optionLe (wordSemOptionAdd (wordSemStackSize ys) opt) t := by
  cases handler <;> cases hsize : wordSemStackSize ys <;> cases opt <;> cases s <;> cases t <;>
    simp_all [wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, optionLe] <;> omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
