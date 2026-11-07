import Flapjack.Compiler.Backend.CopyingGc.Proofs.Progress
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Heap

/-! Data-address case of the abstract-to-word copying-collector simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.WordGcFunctions Flapjack.Compiler.Backend.CopyingGc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem clearLowBit {width : Nat} (value : BitVec width) :
    (value &&& ~~~(1 : BitVec width)) &&& 1 = 0 := by
  rw [BitVec.and_assoc]
  simp

private theorem starEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]

/-- The `Data` case of `word_gc_move_thm`: moving an immediate or code
location leaves the heap and memory unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_move_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGcMove_data {width : Nat} [NeZero width] (conf : Config)
    (value : WordLocW width) (a n limit a1 n1 : Nat)
    (heap heap1 h1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa pa1 i1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (x1 : HeapAddress (WordLocW width)) (w : WordLocW width) (c1 : Bool)
    (abstractRun : gcMove (.data value, [], a, n, heap, true, limit) = (x1, h1, a1, n1, heap1, true))
    (_heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (separated : SetSep.star (SetSep.star (wordHeap curr heap conf) (Misc.wordList pa xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (wordRun : wordGcMove conf (wordAddr conf (.data value), BitVec.ofNat width a, pa, curr, memory, domain) =
      (w, i1, pa1, memory1, c1)) (length : xs.length = n) :
    ∃ xs1,
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap1 conf) (wordHeap pa h1 conf))
        (Misc.wordList pa1 xs1)) frame (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      w = wordAddr conf x1 ∧ heapLength heap1 = heapLength heap ∧ c1 = true ∧
      i1 = BitVec.ofNat width a1 ∧ n1 = xs1.length ∧
      pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength h1) := by
  simp only [gcMove, Prod.mk.injEq] at abstractRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl, _⟩ := abstractRun
  cases value with
  | loc l1 l2 =>
    simp only [wordAddr, wordGcMove, decide_true, Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    refine ⟨xs, ?_, rfl, rfl, rfl, rfl, length.symm, ?_⟩
    · simpa [wordHeap, starEmptyRight] using separated
    · simp [heapLength]
  | word bits =>
    simp only [wordAddr, wordGcMove, clearLowBit, ↓reduceIte, Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    refine ⟨xs, ?_, rfl, rfl, rfl, rfl, length.symm, ?_⟩
    · simpa [wordHeap, starEmptyRight] using separated
    · simp [heapLength]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
