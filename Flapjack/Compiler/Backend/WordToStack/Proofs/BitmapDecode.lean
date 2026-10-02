import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapSentinelLength

namespace Flapjack.Compiler.Backend.WordToStack

/-- Full original bitmap decoding theorem. Every Boolean list is recovered
from its native word-list encoding, independently of arbitrary trailing words.
Only the original dimension-at-least-eight guard is required. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "read_bitmap_word_list"
  (words_as_type_indexed_bitvec)]
theorem readBitmapWordList {width : Nat} [NeZero width] (bits : List Bool)
    (trailing : List (BitVec width)) (hwidth : 8 ≤ width) :
    Flapjack.StackSem.readBitmap (wordListW (bits ++ [true]) (width - 1) ++ trailing) =
      some bits := by
  generalize hn : bits.length = n
  induction n using Nat.strongRecOn generalizing bits with
  | ind n ih =>
    rw [wordListW]
    by_cases hshort : bits.length + 1 ≤ width - 1
    · have hlen : bits.length + 1 < width := by omega
      have hm : (bitsToWordW (bits ++ [true]) : BitVec width).msb = false := by
        rw [BitVec.msb_eq_getLsbD_last]
        apply bitsToWordMiss
        simp only [List.length_append, List.length_cons, List.length_nil]
        constructor <;> omega
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [if_pos (Or.inl hshort)]
      simp only [List.cons_append, List.nil_append, Flapjack.StackSem.readBitmap, hm,
        Bool.false_eq_true, ↓reduceIte]
      rw [bitLengthBitsToWord bits hlen]
      simp only [Nat.add_sub_cancel]
      rw [genlistBitsToWord bits hlen]
    · have hlong : width - 1 ≤ bits.length := by omega
      have htake : (bits.take (width - 1)).length = width - 1 := by
        simp [List.length_take, Nat.min_eq_left hlong]
      have hta : (bits ++ [true]).take (width - 1) = bits.take (width - 1) := by
        exact List.take_append_of_le_length hlong
      have hda : (bits ++ [true]).drop (width - 1) = bits.drop (width - 1) ++ [true] := by
        exact List.drop_append_of_le_length hlong
      have hm : (bitsToWordW (bits.take (width - 1) ++ [true]) : BitVec width).msb = true := by
        rw [BitVec.msb_eq_getLsbD_last,
          BitmapBitStructureSupport.bitmapBitLookup _ _ (by omega), ← htake]
        simp
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [if_neg (by omega), hta, hda]
      simp only [List.cons_append, Flapjack.StackSem.readBitmap, hm, ↓reduceIte]
      have hdrop : (bits.drop (width - 1)).length < n := by
        simp only [List.length_drop]
        omega
      rw [ih _ hdrop (bits.drop (width - 1)) rfl]
      simp only
      have hp := genlistBitsToWordAlt (width := width) (bits.take (width - 1)) [true]
        (by simp only [List.length_append, List.length_cons, List.length_nil, htake]; omega)
      rw [htake] at hp
      rw [hp, List.take_append_drop]

end Flapjack.Compiler.Backend.WordToStack
