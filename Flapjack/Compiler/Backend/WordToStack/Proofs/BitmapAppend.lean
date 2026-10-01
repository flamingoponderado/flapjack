import Flapjack.Compiler.Backend.Semantics.StackSem.StackCodec

namespace Flapjack.WordToStackProofs
open Flapjack.StackSem

/-- A successful bitmap terminates before any subsequently appended words. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "read_bitmap_append_extra"
  (words_as_type_indexed_bitvec)]
theorem readBitmapAppendExtra {width : Nat} [NeZero width]
    (l1 l2 : List (BitVec width)) (bits : List Bool)
    (h : readBitmap l1 = some bits) : readBitmap (l1 ++ l2) = some bits := by
  induction l1 generalizing bits with
  | nil => simp [readBitmap] at h
  | cons word words ih =>
      cases hm : word.msb with
      | false => simpa [readBitmap, hm] using h
      | true =>
          cases hr : readBitmap words with
          | none => simp [readBitmap, hm, hr] at h
          | some tailBits =>
              have ht := ih tailBits hr
              simpa [readBitmap, hm, ht, hr] using h

/-- Appending bitmap words preserves a successful one-based descriptor lookup.
HOL keeps the bitmap-word dimension independent of the descriptor payload-word
dimension; both remain positive and no equality between them is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "full_read_bitmap_append"
  (words_as_type_indexed_bitvec)]
theorem fullReadBitmapAppend {bitmapWidth : Nat} {width : Nat}
    [NeZero bitmapWidth] [NeZero width]
    (bitmaps : List (BitVec bitmapWidth)) (w : WordLocW width) (bits : List Bool)
    (moreBitmaps : List (BitVec bitmapWidth)) (h : fullReadBitmap bitmaps w = some bits) :
    fullReadBitmap (bitmaps ++ moreBitmaps) w = some bits := by
  cases w with
  | loc a b => simp [fullReadBitmap] at h
  | word word =>
      by_cases hz : word = 0
      · simp [fullReadBitmap, hz] at h
      · simp only [fullReadBitmap, if_neg hz] at h ⊢
        have hb : (word - 1).toNat ≤ bitmaps.length := by
          by_cases hb : (word - 1).toNat ≤ bitmaps.length
          · exact hb
          · have he : bitmaps.drop (word - 1).toNat = [] :=
              List.drop_eq_nil_iff.mpr (by omega)
            rw [he] at h
            simp only [readBitmap, reduceCtorEq] at h
        rw [List.drop_append_of_le_length hb]
        exact readBitmapAppendExtra _ _ _ h

end Flapjack.WordToStackProofs
