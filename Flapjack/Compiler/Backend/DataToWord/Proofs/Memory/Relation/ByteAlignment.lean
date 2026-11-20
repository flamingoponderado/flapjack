module

public import Flapjack.Misc.GetByteSetByte
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! Byte-address alignment facts used by the memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.HolByte

/-- Adding a byte-aligned word preserves the byte offset. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "w2n_add_byte_align_lemma"
  (words_as_type_indexed_bitvec)]
theorem toNat_add_byteAlign {width : Nat} [NeZero width] (a a' : BitVec width) :
    goodDimindex width →
    (a' + holByteAlign a).toNat % (width / 8) = a'.toNat % (width / 8) := by
  intro good
  rw [BitVec.toNat_add, holByteAlign_toNat good]
  rcases good with rfl | rfl <;> norm_num

/-- A byte-aligned address does not change the byte read from a word. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "get_byte_byte_align"
  (words_as_type_indexed_bitvec)]
theorem getByte_byteAlign {width : Nat} [NeZero width] (a a' w : BitVec width) (be : Bool) :
    goodDimindex width → getByte (a' + holByteAlign a) w be = getByte a' w be := by
  intro good
  unfold getByte byteIndex
  dsimp only
  rw [toNat_add_byteAlign a a' good]

/-- The byte read depends only on the offset from an aligned address. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "get_byte_eq"
  (words_as_type_indexed_bitvec)]
theorem getByte_eq {width : Nat} [NeZero width] (a a' w : BitVec width) (be : Bool) :
    goodDimindex width ∧ a = holByteAlign a + a' → getByte a w be = getByte a' w be := by
  rintro ⟨good, equal⟩
  rw [equal, BitVec.add_comm]
  exact getByte_byteAlign a a' w be good

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
