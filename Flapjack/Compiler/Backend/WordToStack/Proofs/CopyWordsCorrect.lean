import Flapjack.Compiler.Backend.WordToStack.Proofs.CopyWordsShort
import Flapjack.Compiler.Backend.WordToStack.Proofs.ConstMemoryAppend

namespace Flapjack.Compiler.Backend.WordToStack

/-- Full original constant bitmap copying theorem: arbitrary lists, domain,
memory and modular addresses, with precisely the source address/dimension guards. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_words_correct"
  (words_as_type_indexed_bitvec)]
theorem copyWordsCorrect {width : Nat} [NeZero width]
    (words : List (Bool × BitVec width)) (xs ys : List (BitVec width))
    (address offset : BitVec width) (domain : BitVec width → Prop) [DecidablePred domain]
    (memory : BitVec width → Flapjack.WordLocW width)
    (addresses : Flapjack.wordSemConstAddresses address words
      (fun key => decide (domain key)) = true)
    (dimension : Flapjack.goodDimindex width) :
    Flapjack.StackSemStoreConsts.copyWordsExact xs.length address offset
      (xs ++ constWordsToBitmapW words words.length ++ ys) domain memory =
    some (address + Flapjack.wordSemBytesInWord * BitVec.ofNat width words.length,
      Flapjack.wordSemConstWrites address offset words memory) := by
  have widthLarge : 1 < width := by rcases dimension with h | h <;> omega
  induction words using (measure List.length).wf.induction generalizing xs address memory with
  | h words ih =>
    rw [constWordsToBitmapW]
    split
    · rename_i short
      have bound : words.length < width := by omega
      have notFull : words.length ≠ width - 1 := by omega
      simpa only [notFull, ↓reduceIte] using
        copyWordsShort words xs address offset ys domain memory addresses dimension bound
    · rename_i long
      let head := words.take (width - 1)
      let tail := words.drop (width - 1)
      have headLength : head.length = width - 1 := by
        simp only [head, List.length_take]; omega
      have tailLength : tail.length = words.length - (width - 1) := by simp [tail]
      have splitWords : head ++ tail = words := List.take_append_drop _ _
      have headBound : head.length < width := by omega
      have addressParts := (Flapjack.WordToStackProofs.constAddressesAppend head tail
        (fun key => decide (domain key)) address).mp (by simpa [splitWords] using addresses)
      have headRun := copyWordsShort head xs address offset
        (constWordsToBitmapW tail tail.length ++ ys) domain memory addressParts.1 dimension headBound
      simp only [if_pos headLength] at headRun
      have shorter : tail.length < words.length := by omega
      have tailRun := ih tail shorter (xs ++ chunkToBitmapW head)
        (address + Flapjack.wordSemBytesInWord * BitVec.ofNat width head.length)
        (Flapjack.wordSemConstWrites address offset head memory) addressParts.2
      have bitmapLength : (chunkToBitmapW head).length = head.length + 1 := by
        simp [chunkToBitmapW]
      have nextIndex : (xs ++ chunkToBitmapW head).length = xs.length + (head.length + 1) := by
        simp [bitmapLength]
      simp only [List.append_assoc] at tailRun
      rw [nextIndex] at tailRun
      change Flapjack.StackSemStoreConsts.copyWordsExact xs.length address offset
        (xs ++ (chunkToBitmapW head ++ constWordsToBitmapW tail (words.length - (width - 1))) ++ ys) domain memory = _
      rw [← tailLength]
      simp only [List.append_assoc] at headRun ⊢
      rw [headRun]
      rw [tailRun]
      have memoryAppend := Flapjack.WordToStackProofs.constWritesAppend head tail address offset memory
      rw [splitWords] at memoryAppend
      rw [← memoryAppend]
      have totalLength : head.length + tail.length = words.length := by
        simpa only [List.length_append] using congrArg List.length splitWords
      have addressAppend :
          address + Flapjack.wordSemBytesInWord * BitVec.ofNat width head.length +
            Flapjack.wordSemBytesInWord * BitVec.ofNat width tail.length =
          address + Flapjack.wordSemBytesInWord * BitVec.ofNat width words.length := by
        rw [← totalLength, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
      rw [addressAppend]

end Flapjack.Compiler.Backend.WordToStack
