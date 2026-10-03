import Flapjack.Compiler.Backend.WordToStack.Proofs.ChunkBits
import Flapjack.Misc.GoodDimindex

namespace Flapjack.Compiler.Backend.WordToStack

/-- Full original chunk MSB law. Both source guards are retained, including
its good-dimension guard even though the bit-bound proof works more broadly. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_msb_chunk_to_bits"
  (words_as_type_indexed_bitvec)]
theorem wordMsbChunkToBits {width : Nat} [NeZero width]
    (words : List (Bool × BitVec width)) (bound : words.length < width)
    (_dimension : Flapjack.goodDimindex width) :
    (chunkToBitsW words).msb = decide (words.length = width - 1) := by
  rw [BitVec.msb_eq_getLsbD_last]
  obtain ⟨sentinel, higher⟩ := chunkToBitsBound words bound
  by_cases last : words.length = width - 1
  · simpa [last] using sentinel
  · have strictlyBelow : words.length < width - 1 := by omega
    have lastInRange : width - 1 < width := by omega
    simpa [last] using higher (width - 1) strictlyBelow lastInRange

end Flapjack.Compiler.Backend.WordToStack
