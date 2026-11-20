module

public import Flapjack.Misc.Alignment
public import Flapjack.Misc.GoodDimindex
public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! Byte alignment of word-size strides in the data-to-word memory proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- On a supported architecture, byte alignment is divisibility by the number
of bytes per word. This is shared infrastructure for the collector proofs. -/
theorem byteAligned_iff_divisible {width : Nat} [NeZero width] (word : BitVec width)
    (good : goodDimindex width) : holByteAligned word = true ↔ word.toNat % (width / 8) = 0 := by
  rcases good with rfl | rfl
  · simpa [holByteAligned, show holLOG2 4 = 2 from holLOG_UNIQUE 2 4 2 ⟨by decide, by decide⟩] using
      holAligned_iff 2 word
  · simpa [holByteAligned, show holLOG2 8 = 3 from holLOG_UNIQUE 2 8 3 ⟨by decide, by decide⟩] using
      holAligned_iff 3 word

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- The machine word-size stride is byte-aligned. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "byte_aligned_bytes_in_word"
  (words_as_type_indexed_bitvec)]
theorem byteAlignedBytesInWord {width : Nat} [NeZero width] (good : goodDimindex width) :
    holByteAligned (wordSemBytesInWord : BitVec width) = true := by
  rw [byteAligned_iff_divisible _ good]
  rcases good with rfl | rfl <;> norm_num [wordSemBytesInWord]

/-- Both orders of a machine-word stride multiplication are byte-aligned. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "byte_align_mult_bytes_in_word"
  (words_as_type_indexed_bitvec)]
theorem byteAlignMultBytesInWord {width : Nat} [NeZero width] (word : BitVec width)
    (good : goodDimindex width) :
    holByteAligned (word * wordSemBytesInWord) = true ∧
      holByteAligned (wordSemBytesInWord * word) = true := by
  have aligned : holByteAligned (wordSemBytesInWord * word) = true := by
    rw [byteAligned_iff_divisible _ good]
    rcases good with rfl | rfl <;>
      norm_num [BitVec.toNat_mul, wordSemBytesInWord, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd,
        Nat.mul_mod]
  exact ⟨by simpa [BitVec.mul_comm] using aligned, aligned⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
