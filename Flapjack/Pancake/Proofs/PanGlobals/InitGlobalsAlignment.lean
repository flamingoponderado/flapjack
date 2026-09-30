import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

namespace Flapjack.PanGlobalsInitGlobalsAlignment

open Flapjack

/-- Exact `byte_aligned_bytes_in_word_mul` (pan_globalsProofScript.sml:2088-2096).
`goodDimindex` is HOL's 32-or-64 dimension condition. The existing byte-aligned
fixed-point predicate clears exactly two or three low bits at those widths.
The proof retains modular word multiplication, including products that wrap;
there is no natural-product bound or extra alignment assumption. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "byte_aligned_bytes_in_word_mul"
  (words_as_type_indexed_bitvec)]
theorem byteAlignedBytesInWordMulHOL {width : Nat} [NeZero width]
    (word : BitVec width) :
    goodDimindex width → panGlobalsByteAlignedHOL (panBytesInWord width * word) := by
  intro hwidth
  rcases hwidth with rfl | rfl
  · change BitVec.ofNat 32
      (((BitVec.ofNat 32 4 * word).toNat / 4) * 4) = BitVec.ofNat 32 4 * word
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]
    omega
  · change BitVec.ofNat 64
      (((BitVec.ofNat 64 8 * word).toNat / 8) * 8) = BitVec.ofNat 64 8 * word
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]
    omega

end Flapjack.PanGlobalsInitGlobalsAlignment
