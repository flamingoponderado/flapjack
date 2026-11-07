import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Heap
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListExists
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListMemory

/-! The word-memory assertion for an entirely unused abstract heap. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

private theorem starEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]

/-- An expanded unused heap owns exactly an existential word list of the
requested length, without a nonzero-length or address-bound premise. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_heap_heap_expand"
  (words_as_type_indexed_bitvec)]
theorem wordHeap_heapExpand {addressWidth : Nat} {valueWidth : Nat}
    [NeZero addressWidth] [NeZero valueWidth]
    (address : BitVec addressWidth) (length : Nat) (conf : Config) :
    wordHeap address (heapExpand length : List (HeapElement (WordLocW valueWidth)
      (HeapTag × List (WordLocW valueWidth)))) conf = Misc.wordListExists address length := by
  cases length with
  | zero =>
    simpa [heapExpand, wordHeap] using
      (StackRemove.WordListExists.wordListExistsThm (β := WordLocW valueWidth) address 0).1.symm
  | succ len => simp [heapExpand, wordHeap, wordEl, starEmptyRight]

private theorem wordEl_listExists {addressWidth : Nat} {valueWidth : Nat}
    [NeZero addressWidth] [NeZero valueWidth] (address : BitVec addressWidth)
    (element : HeapElement (WordLocW valueWidth) (HeapTag × List (WordLocW valueWidth)))
    (conf : Config) (heap : (BitVec addressWidth × WordLocW valueWidth) → Prop)
    (assertion : wordEl address element conf heap) :
    Misc.wordListExists address (elLength element) heap := by
  cases element with
  | unused len => exact assertion
  | forwardPointer index value len =>
    simp only [wordEl] at assertion
    simp only [elLength, (StackRemove.WordListExists.wordListExistsThm address len).2,
      SetSep.sepExists]
    exact ⟨.word (BitVec.ofNat valueWidth index <<< (2 : Nat)), assertion⟩
  | dataElement addresses len data =>
    rcases data with ⟨tag, payload⟩
    generalize eqn : wordPayload (headerWidth := valueWidth) addresses len tag payload conf = result at assertion
    rcases result with ⟨header, words, valid⟩
    simp only [wordEl, eqn] at assertion
    obtain ⟨wordList, _, _, validEq⟩ := (StackRemove.WordListExists.starCond _ _ _).mp assertion
    subst valid
    have wordsLen := wordPayloadImp addresses len tag payload conf header words eqn
    simp only [elLength, Misc.wordListExists, SetSep.sepExists]
    refine ⟨.word header :: words, (StackRemove.WordListExists.starCond _ _ _).mpr ⟨wordList, ?_⟩⟩
    simp [wordsLen]

/-- A separated abstract heap element can be forgotten to an existential
word list of its exact length, while preserving an arbitrary external frame. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_el_IMP_word_list_exists"
  (words_as_type_indexed_bitvec)]
theorem wordEl_imp_wordListExists {addressWidth : Nat} {valueWidth : Nat}
    [NeZero addressWidth] [NeZero valueWidth]
    (element : HeapElement (WordLocW valueWidth) (HeapTag × List (WordLocW valueWidth)))
    (frame : ((BitVec addressWidth × WordLocW valueWidth) → Prop) → Prop)
    (address : BitVec addressWidth) (conf : Config)
    (heap : (BitVec addressWidth × WordLocW valueWidth) → Prop)
    (assertion : SetSep.star frame (wordEl address element conf) heap) :
    SetSep.star frame (Misc.wordListExists address (elLength element)) heap := by
  obtain ⟨left, right, split, frameHeap, elementHeap⟩ := assertion
  exact ⟨left, right, split, frameHeap, wordEl_listExists address element conf right elementHeap⟩

/-- A separated abstract heap can be forgotten to an existential word list of
its total length, preserving the same arbitrary frame and predicate heap. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_heap_IMP_word_list_exists"
  (words_as_type_indexed_bitvec)]
theorem wordHeap_imp_wordListExists {addressWidth : Nat} {valueWidth : Nat}
    [NeZero addressWidth] [NeZero valueWidth]
    (elements : List (HeapElement (WordLocW valueWidth) (HeapTag × List (WordLocW valueWidth))))
    (frame : ((BitVec addressWidth × WordLocW valueWidth) → Prop) → Prop)
    (address : BitVec addressWidth) (conf : Config)
    (heap : (BitVec addressWidth × WordLocW valueWidth) → Prop)
    (assertion : SetSep.star frame (wordHeap address elements conf) heap) :
    SetSep.star frame (Misc.wordListExists address (heapLength elements)) heap := by
  induction elements generalizing frame address heap with
  | nil =>
    simpa [wordHeap, heapLength, (StackRemove.WordListExists.wordListExistsThm
      (β := WordLocW valueWidth) address 0).1] using assertion
  | cons head tail ih =>
    simp only [wordHeap, SetSep.starAssoc] at assertion
    obtain ⟨left, right, split, prefixHeap, tailHeap⟩ := assertion
    have headReplaced := wordEl_imp_wordListExists head frame address conf left prefixHeap
    have tailReplaced := ih (SetSep.star frame (Misc.wordListExists address (elLength head)))
      (address + StackRemove.bytesInWord addressWidth * BitVec.ofNat addressWidth (elLength head)) heap
      ⟨left, right, split, headReplaced, tailHeap⟩
    simp only [heapLength, List.map_cons, List.sum_cons,
      StackRemove.Proofs.WordListMemory.wordListExistsAdd, SetSep.starAssoc]
    exact tailReplaced

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
