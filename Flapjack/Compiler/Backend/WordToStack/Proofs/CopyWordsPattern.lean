import Flapjack.Compiler.Backend.WordToStack.Proofs.ChunkBits
import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConsts
import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers

namespace Flapjack.Compiler.Backend.WordToStack

/-- Flapjack infrastructure for the original pattern-copy induction: removing
one encoded low bit recovers the tail under the source chunk-length guard.
HOL proves this inline in copy_words_for_pattern_thm, with no separate named
source declaration. -/
theorem chunkToBitsTail {width : Nat} [NeZero width]
    (bit : Bool) (word : BitVec width) (words : List (Bool × BitVec width))
    (bound : words.length + 1 < width) :
    chunkToBitsW ((bit, word) :: words) >>> (1 : Nat) = chunkToBitsW words := by
  have tailBound : words.length < width := by omega
  have msb : (chunkToBitsW words).msb = false := by
    rw [BitVec.msb_eq_getLsbD_last]
    exact (chunkToBitsBound words tailBound).2 (width - 1) (by omega) (by omega)
  cases bit
  · simpa only [chunkToBitsW, Bool.false_eq_true, ↓reduceIte] using
      shiftShiftLemma (chunkToBitsW words) msb
  · simp only [chunkToBitsW, ↓reduceIte]
    rw [← wordShiftOrOne]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have recovered := congrArg (fun w : BitVec width => w.getLsbD i)
      (shiftShiftLemma (chunkToBitsW words) msb)
    simpa [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_one] using recovered

/-- The full original pattern-copy theorem, over arbitrary prefix/suffix,
address, relocation offset, domain and memory. Only the original chunk length
and constant-address guards are assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_words_for_pattern_thm"
  (words_as_type_indexed_bitvec)]
theorem copyWordsForPatternTheorem {width : Nat} [NeZero width]
    (words : List (Bool × BitVec width)) (xs : List (BitVec width))
    (address offset : BitVec width) (ys : List (BitVec width))
    (domain : BitVec width → Prop) [DecidablePred domain]
    (memory : BitVec width → Flapjack.WordLocW width)
    (bound : words.length < width)
    (addresses : Flapjack.wordSemConstAddresses address words
      (fun key => decide (domain key)) = true) :
    Flapjack.StackSemStoreConsts.copyWordsForPattern (chunkToBitsW words) xs.length
      address offset (xs ++ words.map Prod.snd ++ ys) domain memory =
    some (xs.length + words.length,
      address + Flapjack.wordSemBytesInWord * BitVec.ofNat width words.length,
      Flapjack.wordSemConstWrites address offset words memory) := by
  induction words generalizing xs address memory with
  | nil =>
    simp [chunkToBitsW, Flapjack.StackSemStoreConsts.copyWordsForPattern,
      Flapjack.wordSemConstWrites, NeZero.ne width]
  | cons head tail ih =>
    obtain ⟨bit, word⟩ := head
    have tailBound : tail.length < width := by simp only [List.length_cons] at bound; omega
    have guards : domain address ∧
        Flapjack.wordSemConstAddresses (address + Flapjack.wordSemBytesInWord) tail
          (fun key => decide (domain key)) = true := by
      simpa [Flapjack.wordSemConstAddresses] using addresses
    have sentinel := (chunkToBitsBound ((bit, word) :: tail) bound).1
    have nonzero : chunkToBitsW ((bit, word) :: tail) ≠ 0 := by
      intro equality
      rw [equality] at sentinel
      simp at sentinel
    have notOne : chunkToBitsW ((bit, word) :: tail) ≠ 1 := by
      intro equality
      rw [equality] at sentinel
      simp [BitVec.getLsbD_one] at sentinel
    have indexBound : xs.length < (xs ++ ((bit, word) :: tail).map Prod.snd ++ ys).length := by
      simp
    rw [Flapjack.StackSemStoreConsts.copyWordsForPattern]
    simp only [nonzero, notOne, ↓reduceDIte, ↓reduceIte,
      guards.1, indexBound, and_self]
    rw [chunkToBitsTail bit word tail bound, chunkToBitsZero]
    have element : (xs ++ ((bit, word) :: tail).map Prod.snd ++ ys)[xs.length] = word := by
      simp
    rw [element]
    have recurse := ih (xs ++ [word]) (address + Flapjack.wordSemBytesInWord)
      (fun key => if key = address then Flapjack.WordLocW.word (if bit then word + offset else word)
        else memory key) tailBound guards.2
    simp only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append] at *
    have addressStep : address + Flapjack.wordSemBytesInWord +
        Flapjack.wordSemBytesInWord * BitVec.ofNat width tail.length =
        address + Flapjack.wordSemBytesInWord * BitVec.ofNat width (tail.length + 1) := by
      simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc, BitVec.add_comm]
    rw [addressStep] at recurse
    simpa only [List.length_append, List.length_singleton, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.add_comm 1 tail.length, Flapjack.wordSemBytesInWord, Flapjack.wordSemConstWrites,
      Nat.add_assoc] using recurse

end Flapjack.Compiler.Backend.WordToStack
