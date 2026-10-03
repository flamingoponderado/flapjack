import Flapjack.Compiler.Backend.WordToStack.Proofs.CopyWordsPattern
import Flapjack.Compiler.Backend.WordToStack.Proofs.ChunkBitsMsb

namespace Flapjack.Compiler.Backend.WordToStack

/-- Full original short-chunk copying law. A full-width chunk continues the
actual outer copy evaluator; shorter chunks return the complete memory pair.
The original address, good-dimension and strict-length guards are retained. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_words"
  (words_as_type_indexed_bitvec)]
theorem copyWordsShort {width : Nat} [NeZero width]
    (words : List (Bool × BitVec width)) (xs : List (BitVec width))
    (address offset : BitVec width) (ys : List (BitVec width))
    (domain : BitVec width → Prop) [DecidablePred domain]
    (memory : BitVec width → Flapjack.WordLocW width)
    (addresses : Flapjack.wordSemConstAddresses address words
      (fun key => decide (domain key)) = true)
    (dimension : Flapjack.goodDimindex width) (bound : words.length < width) :
    Flapjack.StackSemStoreConsts.copyWordsExact xs.length address offset
      (xs ++ chunkToBitmapW words ++ ys) domain memory =
    if words.length = width - 1 then
      Flapjack.StackSemStoreConsts.copyWordsExact (xs.length + (words.length + 1))
        (address + Flapjack.wordSemBytesInWord * BitVec.ofNat width words.length)
        offset (xs ++ chunkToBitmapW words ++ ys) domain
        (Flapjack.wordSemConstWrites address offset words memory)
    else some (address + Flapjack.wordSemBytesInWord * BitVec.ofNat width words.length,
      Flapjack.wordSemConstWrites address offset words memory) := by
  have indexBound : xs.length < (xs ++ chunkToBitmapW words ++ ys).length := by
    simp [chunkToBitmapW]
  have read : (xs ++ chunkToBitmapW words ++ ys)[xs.length]! = chunkToBitsW words := by
    simp [chunkToBitmapW]
  have patternCopy := copyWordsForPatternTheorem words (xs ++ [chunkToBitsW words])
    address offset ys domain memory bound addresses
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
    List.append_assoc, List.cons_append, List.nil_append] at patternCopy
  rw [Flapjack.StackSemStoreConsts.copyWordsExact]
  simp only [Nat.not_le.mpr indexBound, ↓reduceDIte, read]
  have sameBitmap : xs ++ chunkToBitmapW words ++ ys =
      xs ++ chunkToBitsW words :: (words.map Prod.snd ++ ys) := by
    simp [chunkToBitmapW]
  rw [sameBitmap] at read
  rw [sameBitmap, read, patternCopy]
  rw [wordMsbChunkToBits words bound dimension]
  have indexEquality : xs.length + 1 + words.length = xs.length + (words.length + 1) := by omega
  rw [indexEquality]
  simp only [decide_eq_true_eq]

end Flapjack.Compiler.Backend.WordToStack
