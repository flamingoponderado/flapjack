import Flapjack.Compiler.Backend.WordToStack
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapWordLemmas

namespace Flapjack.Compiler.Backend.WordToStack

/-- Full original sentinel and higher-bit bound at every positive dimension,
with arbitrary payloads and only the original strict chunk-length guard. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "chunk_to_bits_bound"
  (words_as_type_indexed_bitvec)]
theorem chunkToBitsBound {width : Nat} [NeZero width]
    (words : List (Bool × BitVec width)) (bound : words.length < width) :
    (chunkToBitsW words).getLsbD words.length = true ∧
    ∀ i, words.length < i → i < width →
      (chunkToBitsW words).getLsbD i = false := by
  have positive : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  induction words with
  | nil =>
    constructor
    · simp [chunkToBitsW, positive]
    · intro i hi _
      have nonzero : i ≠ 0 := by simp only [List.length_nil] at hi; omega
      simp [chunkToBitsW, BitVec.getLsbD_one, nonzero]
  | cons head tail ih =>
    obtain ⟨bit, word⟩ := head
    have tailBound : tail.length < width := by simp only [List.length_cons] at bound; omega
    obtain ⟨sentinel, higher⟩ := ih tailBound
    have encoding : chunkToBitsW ((bit, word) :: tail) =
        if bit then (chunkToBitsW tail <<< 1) ||| 1 else chunkToBitsW tail <<< 1 := by
      cases bit
      · rfl
      · exact (wordShiftOrOne (chunkToBitsW tail)).symm
    have fullBound : tail.length + 1 < width := bound
    rw [encoding]
    constructor
    · cases bit <;>
        simp [-BitVec.getLsbD_eq_getElem,
          BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, sentinel, fullBound]
    · intro i hi hwidth
      have previous : tail.length < i - 1 := by simp only [List.length_cons] at hi; omega
      have previousWidth : i - 1 < width := by omega
      have nonzero : i ≠ 0 := by simp only [List.length_cons] at hi; omega
      have shift : 1 ≤ i := by omega
      cases bit <;>
        simp [-BitVec.getLsbD_eq_getElem,
          BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, hwidth, nonzero,
          higher _ previous previousWidth]

/-- Full original unconditional low-bit law, including chunks at or beyond
word capacity. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "chunk_to_bits_0"
  (words_as_type_indexed_bitvec)]
theorem chunkToBitsZero {width : Nat} [NeZero width]
    (bit : Bool) (word : BitVec width) (words : List (Bool × BitVec width)) :
    (chunkToBitsW ((bit, word) :: words)).getLsbD 0 = bit := by
  have positive : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  cases bit
  · simp [chunkToBitsW]
  · simp only [chunkToBitsW, ↓reduceIte]
    rw [← wordShiftOrOne]
    simp [positive]

end Flapjack.Compiler.Backend.WordToStack
