module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ListSimulation

@[expose] public section

/-! Empty-pending-heap case of the collector scan simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.CopyingGc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The empty-pending constructor case retains every premise and conclusion
of the collector scan theorem. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_move_loop_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGcMoveLoop_empty {width : Nat} [NeZero width] (conf : Config)
    (scanned : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a n : Nat) (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (c0 : Bool) (limit : Nat)
    (h11 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (a1 n1 : Nat)
    (heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (i1 pa1 : BitVec width) (m1 : BitVec width → WordLocW width) (c1 : Bool)
    (xs : List (WordLocW width)) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (m : BitVec width → WordLocW width) (k : Nat) (curr new : BitVec width)
    (dm : BitVec width → Bool)
    (abstractRun : gcMoveLoop (scanned, [], a, n, heap, c0, limit) = (h11, a1, n1, heap1, true))
    (_cTrue : c0 = true)
    (_heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (_byteBound : heapLength heap * (width / 8) < 2 ^ width)
    (_lenBound : conf.lenSize + 2 < width)
    (separated : SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap conf)
      (wordHeap new (scanned ++ []) conf))
      (Misc.wordList (new + BitVec.ofNat width (heapLength (scanned ++ [])) * wordSemBytesInWord) xs)) frame
      (SetSep.fun2Set (m, fun address => dm address = true)))
    (_steps : limit - heapLength scanned ≤ k) (_limit : limit = heapLength heap)
    (_good : goodDimindex width)
    (wordRun : wordGcMoveLoop k conf (new + BitVec.ofNat width (heapLength scanned) * wordSemBytesInWord,
      BitVec.ofNat width a, new + BitVec.ofNat width (heapLength (scanned ++ [])) * wordSemBytesInWord,
      curr, m, dm, true) = (i1, pa1, m1, c1)) (length : xs.length = n) :
    ∃ xs1,
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap1 conf) (wordHeap new h11 conf))
        (Misc.wordList pa1 xs1)) frame (SetSep.fun2Set (m1, fun address => dm address = true)) ∧
      heapLength heap1 = heapLength heap ∧ c1 = true ∧ i1 = BitVec.ofNat width a1 ∧ n1 = xs1.length ∧
      pa1 = new + wordSemBytesInWord * BitVec.ofNat width (heapLength h11) := by
  simp only [gcMoveLoop, Prod.mk.injEq] at abstractRun
  obtain ⟨rfl, rfl, rfl, rfl, _⟩ := abstractRun
  simp only [List.append_nil] at wordRun separated
  rw [wordGcMoveLoop] at wordRun
  simp only [↓reduceIte, Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl⟩ := wordRun
  exact ⟨xs, separated, rfl, rfl, rfl, length.symm, by simp [BitVec.mul_comm]⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
