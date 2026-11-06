import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Move
import Flapjack.Compiler.Backend.CopyingGc.Proofs.Append
import Flapjack.Compiler.Backend.CopyingGc.Proofs.Progress

/-! Simulation of the copying collector over the entire root list. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.CopyingGc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem starEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]

private theorem frameCopied {α : Type} (h c w f : (α → Prop) → Prop) :
    SetSep.star (SetSep.star (SetSep.star h c) w) f =
      SetSep.star (SetSep.star h w) (SetSep.star c f) := by
  simp only [← SetSep.starAssoc]
  rw [star_swap_first c w]

private theorem combineCopied {α : Type} (h t w c f : (α → Prop) → Prop) :
    SetSep.star (SetSep.star (SetSep.star h t) w) (SetSep.star c f) =
      SetSep.star (SetSep.star (SetSep.star h (SetSep.star c t)) w) f := by
  simp only [← SetSep.starAssoc]
  rw [star_swap_first w c, star_swap_first t c]

/-- The original root-list simulation, preserving the full separated heap,
the mapped roots, allocation indices, status and output free-space suffix. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_move_roots_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGcMoveRoots_thm {width : Nat} [NeZero width] (conf : Config)
    (roots : List (HeapAddress (WordLocW width))) :
    ∀ (a n : Nat) (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (limit : Nat) (pa : BitVec width) (roots1 : List (HeapAddress (WordLocW width)))
      (h1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (a1 n1 : Nat) (heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (pa1 : BitVec width) (memory memory1 : BitVec width → WordLocW width)
      (xs : List (WordLocW width)) (i1 : BitVec width) (c1 : Bool) (w : List (WordLocW width))
      (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
      (curr : BitVec width) (domain : BitVec width → Bool),
      gcMoveList (roots, [], a, n, heap, true, limit) = (roots1, h1, a1, n1, heap1, true) →
      heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf →
      SetSep.star (SetSep.star (wordHeap curr heap conf) (Misc.wordList pa xs)) frame
        (SetSep.fun2Set (memory, fun address => domain address = true)) →
      wordGcMoveRoots conf (roots.map (wordAddr conf), BitVec.ofNat width a, pa, curr, memory, domain) =
        (w, i1, pa1, memory1, c1) → xs.length = n →
      ∃ xs1,
        SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap1 conf) (wordHeap pa h1 conf))
          (Misc.wordList pa1 xs1)) frame (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
        w = roots1.map (wordAddr conf) ∧ heapLength heap1 = heapLength heap ∧ c1 = true ∧
        i1 = BitVec.ofNat width a1 ∧ n1 = xs1.length ∧
        pa1 = pa + BitVec.ofNat width (heapLength h1) * wordSemBytesInWord := by
  induction roots with
  | nil =>
    intro a n heap limit pa roots1 h1 a1 n1 heap1 pa1 memory memory1 xs i1 c1 w frame curr domain
      abstractRun _ separated wordRun length
    simp only [gcMoveList, Prod.mk.injEq] at abstractRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl, _⟩ := abstractRun
    simp only [List.map_nil, wordGcMoveRoots, Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    refine ⟨xs, ?_, rfl, rfl, rfl, rfl, length.symm, ?_⟩
    · simpa [wordHeap, starEmptyRight] using separated
    · simp [heapLength]
  | cons root roots ih =>
    intro a n heap limit pa roots1 h1 a1 n1 heap1 pa1 memory memory1 xs i1 c1 w frame curr domain
      abstractRun bound separated wordRun length
    simp only [gcMoveList] at abstractRun
    generalize headRun : gcMove (root, [], a, n, heap, true, limit) = headResult at abstractRun
    rcases headResult with ⟨root', copied, a', n', heap', status⟩
    rw [gcMoveList_alt roots copied a' n' heap' status limit () () () () () ()] at abstractRun
    generalize tailRun : gcMoveList (roots, [], a', n', heap', status, limit) = tailResult at abstractRun
    rcases tailResult with ⟨roots', copied', a'', n'', heap'', status'⟩
    simp only [Prod.mk.injEq] at abstractRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := abstractRun
    have statusTrue : status = true :=
      (gcMoveList_ok roots roots' [] copied' heap' heap'' a' n' limit a'' n'' 0 status () tailRun).1
    subst status
    simp only [List.map_cons, wordGcMoveRoots] at wordRun
    generalize wordHeadRun : wordGcMove conf (wordAddr conf root, BitVec.ofNat width a, pa, curr, memory, domain) =
      wordHeadResult at wordRun
    rcases wordHeadResult with ⟨wordRoot, iHead, paHead, memoryHead, okHead⟩
    generalize wordTailRun : wordGcMoveRoots conf (roots.map (wordAddr conf), iHead, paHead, curr, memoryHead, domain) =
      wordTailResult at wordRun
    rcases wordTailResult with ⟨wordRoots, iTail, paTail, memoryTail, okTail⟩
    simp only [Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    obtain ⟨freeHead, headSep, rootEq, heapLen, headOk, indexEq, freeLen, paEq⟩ :=
      wordGcMove_thm conf root root' a n limit a' n' heap heap' copied curr pa paHead iHead xs
        memory memoryHead domain frame wordRoot okHead headRun bound separated wordHeadRun length
    have tailSep : SetSep.star (SetSep.star (wordHeap curr heap' conf) (Misc.wordList paHead freeHead))
        (SetSep.star (wordHeap pa copied conf) frame)
        (SetSep.fun2Set (memoryHead, fun address => domain address = true)) := by
      rw [← frameCopied]
      exact headSep
    have bound' : heapLength heap' ≤ 2 ^ width / 2 ^ shiftLength conf := by simpa [heapLen] using bound
    have wordTailRun' : wordGcMoveRoots conf
        (roots.map (wordAddr conf), BitVec.ofNat width a', paHead, curr, memoryHead, domain) =
          (wordRoots, iTail, paTail, memoryTail, okTail) := by simpa [indexEq] using wordTailRun
    obtain ⟨freeTail, tailSep, rootsEq, heapLen', tailOk, indexEq', freeLen', paEq'⟩ :=
      ih a' n' heap' limit paHead roots' copied' a'' n'' heap'' paTail memoryHead memoryTail freeHead
        iTail okTail wordRoots (SetSep.star (wordHeap pa copied conf) frame) curr domain
        tailRun bound' tailSep wordTailRun' freeLen.symm
    refine ⟨freeTail, ?_, ?_, heapLen'.trans heapLen, ?_, indexEq', freeLen', ?_⟩
    · rw [combineCopied] at tailSep
      rw [wordHeapAppend]
      have paEq'': paHead = pa + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength copied) := by
        simpa [wordSemBytesInWord, StackRemove.bytesInWord] using paEq
      simpa only [paEq''] using tailSep
    · simp [rootEq, rootsEq]
    · simp [headOk, tailOk]
    · rw [paEq', paEq]
      simp only [heapLength_append, BitVec.ofNat_add, BitVec.add_mul]
      ac_rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
