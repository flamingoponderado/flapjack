import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Representation
import Flapjack.Compiler.Backend.WordGcFunctions
import Flapjack.Misc.WordList
import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeap

/-! Separation assertions for the data-to-word abstract heap. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

/-- The word-level assertion for one abstract heap element. The address word
width and the stored word width are independently quantified in the HOL
definition; in particular, the payload length bound uses the address width. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_el_def"
  (words_as_type_indexed_bitvec)]
def wordEl {addressWidth : Nat} {valueWidth : Nat} [NeZero addressWidth] [NeZero valueWidth]
    (address : BitVec addressWidth)
    (element : HeapElement (WordLocW valueWidth) (HeapTag × List (WordLocW valueWidth)))
    (conf : Config) : ((BitVec addressWidth × WordLocW valueWidth) → Prop) → Prop :=
  match element with
  | .unused len => Misc.wordListExists address (len + 1)
  | .forwardPointer index _ len =>
      SetSep.star (SetSep.one (address, WordLocW.word (BitVec.ofNat valueWidth index <<< (2 : Nat))))
        (Misc.wordListExists (address + StackRemove.bytesInWord addressWidth) len)
  | .dataElement addresses len (tag, payload) =>
      let (header, words, valid) := wordPayload addresses len tag payload conf
      SetSep.star (Misc.wordList address (.word header :: words))
        (SetSep.cond (words.length < 2 ^ (addressWidth - 4) ∧
          WordGcFunctions.decodeLength conf header = BitVec.ofNat valueWidth words.length ∧ valid = true))

/-- The separated assertions for an abstract heap, laid out in source order
with modular address arithmetic. Address and stored word widths are independent. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_heap_def"
  (words_as_type_indexed_bitvec)]
def wordHeap {addressWidth : Nat} {valueWidth : Nat} [NeZero addressWidth] [NeZero valueWidth]
    (address : BitVec addressWidth) :
    List (HeapElement (WordLocW valueWidth) (HeapTag × List (WordLocW valueWidth))) →
      Config → ((BitVec addressWidth × WordLocW valueWidth) → Prop) → Prop
  | [], _ => SetSep.emp
  | element :: rest, conf =>
      SetSep.star (wordEl address element conf)
        (wordHeap (address + StackRemove.bytesInWord addressWidth * BitVec.ofNat addressWidth (elLength element)) rest conf)

/-- A heap append separates into the prefix and the suffix, whose starting
address is advanced by the total length of the prefix. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_heap_APPEND"
  (words_as_type_indexed_bitvec)]
theorem wordHeapAppend {addressWidth : Nat} {valueWidth : Nat} [NeZero addressWidth] [NeZero valueWidth]
    (xs ys : List (HeapElement (WordLocW valueWidth) (HeapTag × List (WordLocW valueWidth))))
    (address : BitVec addressWidth) (conf : Config) :
    wordHeap address (xs ++ ys) conf =
      SetSep.star (wordHeap address xs conf)
        (wordHeap (address + StackRemove.bytesInWord addressWidth * BitVec.ofNat addressWidth (heapLength xs)) ys conf) := by
  induction xs generalizing address with
  | nil => simp [wordHeap, heapLength, StackRemove.StackHeap.starEmptyLeft]
  | cons head tail ih =>
    simp only [List.cons_append, wordHeap, ih, heapLength, List.map_cons, List.sum_cons]
    rw [← SetSep.starAssoc]
    congr 2
    congr 1
    simp only [BitVec.ofNat_add, BitVec.mul_add]
    ac_rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
