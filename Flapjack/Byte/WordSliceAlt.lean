import Flapjack.Byte

namespace Flapjack.HolByte

/-- Literal HOL FCP slice: retain exactly those bits whose indices lie in the
half-open interval [low, high). Arbitrary bounds, including inverted intervals
and bounds above the word dimension, are part of the original definition. -/
@[hol "HOL/src/n-bit/byteScript.sml" "word_slice_alt_def"
  (words_as_type_indexed_bitvec)]
def wordSliceAlt {width : Nat} [NeZero width] (high low : Nat)
    (word : BitVec width) : BitVec width :=
  (BitVec.ofBoolListLE (List.ofFn (fun index : Fin width =>
    decide (low ≤ index.val ∧ index.val < high) && word.getLsbD index.val))).cast
      (by simp)

/-- Flapjack infrastructure exposing the original FCP equation at every
in-range bit, without hypotheses on the two slice bounds. -/
theorem wordSliceAlt_bit {width : Nat} [NeZero width] (high low : Nat)
    (word : BitVec width) (index : Fin width) :
    (wordSliceAlt high low word).getLsbD index.val =
      (decide (low ≤ index.val ∧ index.val < high) && word.getLsbD index.val) := by
  change (BitVec.ofBoolListLE (List.ofFn (fun i : Fin width =>
    decide (low ≤ i.val ∧ i.val < high) && word.getLsbD i.val))).getLsbD index.val = _
  rw [BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD]

end Flapjack.HolByte
