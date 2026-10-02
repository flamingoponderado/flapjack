import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapBitStructure
import Flapjack.Compiler.Backend.Semantics.StackSem.WordBitmap

namespace Flapjack.Compiler.Backend.WordToStack

/-- Flapjack infrastructure: the appended sentinel is an in-range true bit,
so the native encoded word is nonzero. No total HOL EL operation is used. -/
private theorem sentinelNonzero {width : Nat} [NeZero width] (bits : List Bool)
    (h : bits.length < width) : (bitsToWordW (bits ++ [true]) : BitVec width) ≠ 0 := by
  intro hz
  have hb := BitmapBitStructureSupport.bitmapBitLookup (width := width)
    (bits ++ [true]) bits.length h
  simp [hz] at hb

/-- Flapjack infrastructure: the literal low bit vanishes after one right shift. -/
private theorem oneRight {width : Nat} [NeZero width] : (1 : BitVec width) >>> 1 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_one]

/-- Full original sentinel bit-length theorem under exactly the original
strict dimension bound, for every Boolean list and positive word width. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "bit_length_bits_to_word"
  (words_as_type_indexed_bitvec)]
theorem bitLengthBitsToWord {width : Nat} [NeZero width] (bits : List Bool)
    (h : bits.length + 1 < width) :
    Flapjack.StackSem.bitLength (bitsToWordW (bits ++ [true]) : BitVec width) = bits.length + 1 := by
  induction bits with
  | nil =>
    have he : (bitsToWordW ([] ++ [true]) : BitVec width) = 1 := by simp [bitsToWordW]
    have h1 : (1 : BitVec width) ≠ 0 := by
      rw [← he]
      apply sentinelNonzero
      simp only [List.length_nil]
      simp only [List.length_nil] at h
      omega
    rw [he, Flapjack.StackSem.bitLength, if_neg h1, oneRight]
    rw [Flapjack.StackSem.bitLength, if_pos rfl]
    rfl
  | cons bit bits ih =>
    have ht : bits.length + 1 < width := by simp at h; omega
    have hm : (bitsToWordW (bits ++ [true]) : BitVec width).msb = false := by
      rw [BitVec.msb_eq_getLsbD_last]
      apply bitsToWordMiss
      simp only [List.length_append, List.length_cons, List.length_nil]
      constructor <;> omega
    have hs := shiftShiftLemma (bitsToWordW (bits ++ [true]) : BitVec width) hm
    have hn := sentinelNonzero (width := width) (bit :: bits) (by simp at h ⊢; omega)
    rw [Flapjack.StackSem.bitLength, if_neg hn]
    have hr : (bitsToWordW ((bit :: bits) ++ [true]) : BitVec width) >>> 1 =
        bitsToWordW (bits ++ [true]) := by
      cases bit
      · simpa only [List.cons_append, bitsToWordW] using hs
      · simp only [List.cons_append, bitsToWordW, BitVec.ushiftRight_or_distrib, hs]
        rw [oneRight]
        simp
    rw [hr, ih ht]
    simp

/-- Full original terminal-word prefix recovery with the original strict
sentinel dimension guard; GENLIST is a mapped natural range. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "GENLIST_bits_to_word"
  (words_as_type_indexed_bitvec)]
theorem genlistBitsToWord {width : Nat} [NeZero width] (bits : List Bool)
    (h : bits.length + 1 < width) :
    (List.range bits.length).map
      (fun i => (bitsToWordW (bits ++ [true]) : BitVec width).getLsbD i) = bits := by
  apply genlistBitsToWordAlt
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

end Flapjack.Compiler.Backend.WordToStack
