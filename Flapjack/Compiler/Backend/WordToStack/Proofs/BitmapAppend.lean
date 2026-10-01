import Flapjack.Compiler.Backend.Semantics.StackSem.StackCodec
import Flapjack.HolRef

/-! Exact append stability of the Word-to-Stack bitmap readers. Appending words
past the end of a successful `read_bitmap`/`full_read_bitmap` decode does not
change the decoded bits, matching the HOL `word_to_stackProofScript.sml`
theorems `read_bitmap_append_extra` and `full_read_bitmap_append`. -/
namespace Flapjack.WordToStackProofs

open Flapjack.StackSem

/-- Appending extra words to a bitmap list that already decodes successfully
does not change the decoded bits. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "read_bitmap_append_extra"
  (words_as_type_indexed_bitvec)]
theorem readBitmapAppendExtra {width : Nat} [NeZero width]
    (l1 l2 : List (BitVec width)) (bits : List Bool) :
    readBitmap l1 = some bits → readBitmap (l1 ++ l2) = some bits := by
  induction l1 generalizing bits with
  | nil => simp [readBitmap]
  | cons word ws ih =>
    intro h
    simp only [readBitmap, List.cons_append] at h ⊢
    by_cases hmsb : word.msb
    · simp only [if_pos hmsb] at h ⊢
      cases hw : readBitmap ws with
      | none => rw [hw] at h; simp at h
      | some rest =>
        rw [hw] at h
        have hws := ih rest hw
        rw [hws]
        exact h
    · simp only [if_neg hmsb] at h ⊢
      exact h

/-- Appending extra bitmap words does not change a successful descriptor
decode. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "full_read_bitmap_append"
  (words_as_type_indexed_bitvec)]
theorem fullReadBitmapAppend {bitmapWidth : Nat} {width : Nat} [NeZero bitmapWidth]
    [NeZero width]
    (bitmaps moreBitmaps : List (BitVec bitmapWidth)) (w : WordLocW width) (bits : List Bool) :
    fullReadBitmap bitmaps w = some bits →
      fullReadBitmap (bitmaps ++ moreBitmaps) w = some bits := by
  intro h
  cases w with
  | word word =>
    by_cases hw : word = 0
    · simp [fullReadBitmap, hw] at h
    · simp only [fullReadBitmap, if_neg hw] at h ⊢
      have hnil : bitmaps.drop (word - 1).toNat ≠ [] := by
        intro hl
        rw [hl] at h
        simp [readBitmap] at h
      have hn : (word - 1).toNat ≤ bitmaps.length := by
        by_cases hle : (word - 1).toNat ≤ bitmaps.length
        · exact hle
        · have hlen : bitmaps.length ≤ (word - 1).toNat := by omega
          exact absurd (List.drop_eq_nil_of_le hlen) hnil
      rw [List.drop_append_of_le_length hn]
      exact readBitmapAppendExtra _ _ _ h
  | loc block offset =>
    simp [fullReadBitmap] at h

end Flapjack.WordToStackProofs
