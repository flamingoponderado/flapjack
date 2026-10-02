import Flapjack.Compiler.Backend.WordToStack
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapWordLemmas

namespace Flapjack.Compiler.Backend.WordToStack

/-- Flapjack infrastructure: combined total Bool-list lookup with false default
and in-range word-bit decoding. This Option/default statement has no separate
HOL original and does not use the provisional total EL/HD operations. -/
private theorem bitmapBitLookup {width : Nat} [NeZero width]
    (bits : List Bool) (i : Nat) (hi : i < width) :
    (bitsToWordW (width := width) bits).getLsbD i = bits[i]?.getD false := by
  induction bits generalizing i with
  | nil => simp [bitsToWordW]
  | cons bit bits ih =>
    cases i with
    | zero =>
      cases bit <;> simp [bitsToWordW, hi]
    | succ i =>
      have hi' : i < width := by omega
      have hb : (bitsToWordW (width := width) bits)[i] = bits[i]?.getD false := by
        rw [← BitVec.getLsbD_eq_getElem hi']
        exact ih i hi'
      cases bit <;> simp [bitsToWordW, hi, hb]

/-- Full original out-of-range-list bit result under the original word-index
and list-length guards; no list element or total-EL default is inspected. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "bits_to_word_miss"
  (words_as_type_indexed_bitvec)]
theorem bitsToWordMiss {width : Nat} [NeZero width] (bits : List Bool) (i : Nat)
    (h : i < width ∧ bits.length ≤ i) :
    (bitsToWordW bits : BitVec width).getLsbD i = false := by
  rw [bitmapBitLookup bits i h.1]
  simp [List.getElem?_eq_none h.2]

/-- Full original SNOC equation, including arbitrary truncating lists. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "bits_to_word_SNOC"
  (words_as_type_indexed_bitvec)]
theorem bitsToWordSnoc {width : Nat} [NeZero width] (bits : List Bool) (bit : Bool) :
    bitsToWordW (bits ++ [bit]) =
      ((if bit then (1 : BitVec width) else 0) <<< bits.length) ||| bitsToWordW bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bitmapBitLookup (bits ++ [bit]) i hi]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, bitmapBitLookup bits i hi]
  by_cases hlt : i < bits.length
  · simp [List.getElem?_append, hlt, hi]
  · by_cases heq : i = bits.length
    · subst i
      cases bit <;> simp [hi, show 0 < width by omega]
    · have hgt : bits.length < i := by omega
      cases bit <;> simp [List.getElem?_append, hlt, hi,
        BitVec.getLsbD_one, show i - bits.length ≠ 0 by omega]

/-- Full original prefix reconstruction under exactly the combined length
bound. GENLIST is the natural range mapped by the word-bit function. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "GENLIST_bits_to_word_alt"
  (words_as_type_indexed_bitvec)]
theorem genlistBitsToWordAlt {width : Nat} [NeZero width] (xs ys : List Bool)
    (h : (xs ++ ys).length ≤ width) :
    (List.range xs.length).map (fun i => (bitsToWordW (xs ++ ys) : BitVec width).getLsbD i) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_range]
    rw [bitmapBitLookup (xs ++ ys) i (by simpa using (show i < width by simp at h; omega))]
    simp [List.getElem?_append, hi2]

end Flapjack.Compiler.Backend.WordToStack
