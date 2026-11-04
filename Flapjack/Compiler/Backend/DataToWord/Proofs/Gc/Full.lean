import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Loop
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.HeapExpand

/-! Simulation of the full copying collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.CopyingGc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private instance {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
private instance {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

private theorem extractFree {width : Nat} [NeZero width] {β : Type}
    (p f : ((BitVec width × β) → Prop) → Prop) (address : BitVec width) (n : Nat)
    (heap : (BitVec width × β) → Prop)
    (h : SetSep.star (SetSep.star p (Misc.wordListExists address n)) f heap) :
    ∃ xs : List β, xs.length = n ∧ SetSep.star (SetSep.star p (Misc.wordList address xs)) f heap := by
  obtain ⟨left, right, split, ⟨a, b, split', ha, hb⟩, hf⟩ := h
  obtain ⟨xs, hx, hn⟩ := (show ∃ xs : List β, Misc.wordList address xs b ∧ xs.length = n by
    simpa only [Misc.wordListExists, SetSep.sepExists, StackRemove.WordListExists.starCond] using hb)
  exact ⟨xs, hn, left, right, split, ⟨a, b, split', ha, hx⟩, hf⟩

private theorem packFree {width : Nat} [NeZero width] {β : Type}
    (p f : ((BitVec width × β) → Prop) → Prop) (address : BitVec width) (xs : List β) (n : Nat)
    (heap : (BitVec width × β) → Prop) (length : xs.length = n)
    (h : SetSep.star (SetSep.star p (Misc.wordList address xs)) f heap) :
    SetSep.star (SetSep.star p (Misc.wordListExists address n)) f heap := by
  obtain ⟨left, right, split, ⟨a, b, split', ha, hb⟩, hf⟩ := h
  refine ⟨left, right, split, ⟨a, b, split', ha, ?_⟩, hf⟩
  exact ⟨xs, (StackRemove.WordListExists.starCond _ _ _).mpr ⟨hb, length⟩⟩

/-- Successful full collection preserves the configured heap limit and
returns an allocation index within it. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "full_gc_IMP"]
theorem fullGc_imp {α β : Type} (roots result : List (HeapAddress α))
    (heap heap1 : List (HeapElement α β)) (limit a : Nat)
    (run : fullGc (roots, heap, limit) = (result, heap1, a, true)) :
    a ≤ limit ∧ limit = heapLength heap := by
  simp only [fullGc] at run
  generalize gcMoveList (roots, [], 0, limit, heap, true, limit) = r at run
  rcases r with ⟨roots1, pending, a1, n1, heapMid, ok⟩
  generalize gcMoveLoop ([], pending, a1, n1, heapMid, ok, limit) = r at run
  rcases r with ⟨scanned, a2, n2, heapEnd, ok2⟩
  simp only [Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq] at run
  obtain ⟨_, _, rfl, ⟨⟨⟨⟨_, _⟩, _⟩, limitEq⟩, _⟩, bound⟩ := run
  exact ⟨bound, limitEq.symm⟩

/-- The successful full-collection result reports the actual length of the
copied heap. This is a local consequence of the source definition. -/
theorem fullGc_alloc {α β : Type} (roots result : List (HeapAddress α))
    (heap heap1 : List (HeapElement α β)) (limit a : Nat)
    (run : fullGc (roots, heap, limit) = (result, heap1, a, true)) :
    a = heapLength heap1 := by
  simp only [fullGc] at run
  generalize gcMoveList (roots, [], 0, limit, heap, true, limit) = r at run
  rcases r with ⟨roots1, pending, a1, n1, heapMid, ok⟩
  generalize gcMoveLoop ([], pending, a1, n1, heapMid, ok, limit) = r at run
  rcases r with ⟨scanned, a2, n2, heapEnd, ok2⟩
  simp only [Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq] at run
  obtain ⟨_, rfl, rfl, ⟨⟨⟨⟨_, allocEq⟩, _⟩, _⟩, _⟩, _⟩ := run
  exact allocEq

/-- Full abstract-to-word copying collection. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_full_gc_thm"
  (words_as_type_indexed_bitvec)]
theorem wordFullGc_thm {width : Nat} [NeZero width] (conf : Config)
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (limit a1 : Nat) (curr new : BitVec width) (m m1 : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (rs1 : List (WordLocW width)) (i1 pa1 : BitVec width) (c1 : Bool)
    (abstractRun : fullGc (roots, heap, limit) = (roots1, heap1, a1, true))
    (heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (byteBound : heapLength heap * (width / 8) < 2 ^ width)
    (lenBound : conf.lenSize + 2 < width)
    (separated : SetSep.star (SetSep.star (wordHeap curr heap conf)
      (wordHeap new (heapExpand limit) conf)) frame
      (SetSep.fun2Set (m, fun address => dm address = true)))
    (limitEq : limit = heapLength heap) (good : goodDimindex width)
    (wordRun : wordFullGc conf (roots.map (wordAddr conf), new, curr, m, dm) =
      (rs1, i1, pa1, m1, c1)) :
    SetSep.star (SetSep.star (wordHeap new (heap1 ++ heapExpand (limit - a1)) conf)
      (wordHeap curr (heapExpand limit) conf)) frame
      (SetSep.fun2Set (m1, fun address => dm address = true)) ∧
    c1 = true ∧ i1 = BitVec.ofNat width a1 ∧ rs1 = roots1.map (wordAddr conf) ∧
    pa1 = new + wordSemBytesInWord * BitVec.ofNat width a1 := by
  simp only [fullGc] at abstractRun
  generalize rootsRun : gcMoveList (roots, [], 0, limit, heap, true, limit) = rootsResult at abstractRun
  rcases rootsResult with ⟨moved, pending, a, n, heapMid, ok⟩
  generalize loopRun : gcMoveLoop ([], pending, a, n, heapMid, ok, limit) = loopResult at abstractRun
  rcases loopResult with ⟨scanned, finalA, finalN, heapFinal, finalOk⟩
  simp only [Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq] at abstractRun
  obtain ⟨rfl, rfl, rfl, ⟨⟨⟨⟨finalOkTrue, allocEq⟩, finalHeapLen⟩, _⟩, freeEq⟩, allocBound⟩ := abstractRun
  subst finalOk
  have okTrue : ok = true := gcMoveLoop_ok [] pending heapMid heapFinal a n limit finalA finalN ok scanned loopRun
  subst ok
  rw [wordHeap_heapExpand] at separated
  obtain ⟨free, freeLen, separated⟩ := extractFree (wordHeap curr heap conf) frame new limit _ separated
  simp only [wordFullGc] at wordRun
  generalize wordRootsRun : wordGcMoveRoots conf (roots.map (wordAddr conf), 0, new, curr, m, dm) = wr at wordRun
  rcases wr with ⟨movedWords, wordA, wordPa, wordMem, wordOk⟩
  generalize wordLoopRun : wordGcMoveLoop (2 ^ width) conf (new, wordA, wordPa, curr, wordMem, dm, wordOk) = wl at wordRun
  rcases wl with ⟨wordFinalA, wordFinalPa, wordFinalMem, wordFinalOk⟩
  simp only [Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
  obtain ⟨freeMid, sepMid, movedEq, midLen, wordOkTrue, wordAEq, freeMidLen, wordPaEq⟩ :=
    wordGcMoveRoots_thm conf roots 0 limit heap limit new moved pending a n heapMid wordPa m wordMem
      free wordA wordOk movedWords frame curr dm rootsRun heapBound separated wordRootsRun freeLen
  subst wordOk
  have boundMid : heapLength heapMid ≤ 2 ^ width / 2 ^ shiftLength conf := by simpa [midLen] using heapBound
  have bytesMid : heapLength heapMid * (width / 8) < 2 ^ width := by simpa [midLen] using byteBound
  have steps : limit - heapLength ([] : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) ≤ 2 ^ width := by
    have divBound : heapLength heap ≤ 2 ^ width := le_trans heapBound (Nat.div_le_self _ _)
    simpa [heapLength, limitEq] using divBound
  have loopConcrete : wordGcMoveLoop (2 ^ width) conf
      (new + BitVec.ofNat width (heapLength ([] : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))) * wordSemBytesInWord,
       BitVec.ofNat width a, new + BitVec.ofNat width (heapLength ([] ++ pending)) * wordSemBytesInWord,
       curr, wordMem, dm, true) = (wordFinalA, wordFinalPa, wordFinalMem, wordFinalOk) := by
    simpa [heapLength, wordAEq, wordPaEq] using wordLoopRun
  have sepLoop : SetSep.star (SetSep.star (SetSep.star (wordHeap curr heapMid conf)
      (wordHeap new ([] ++ pending) conf))
      (Misc.wordList (new + BitVec.ofNat width (heapLength ([] ++ pending)) * wordSemBytesInWord) freeMid)) frame
      (SetSep.fun2Set (wordMem, fun address => dm address = true)) := by
    simpa [wordPaEq] using sepMid
  obtain ⟨freeFinal, sepFinal, finalLen, c1True, i1Eq, freeFinalLen, pa1Eq⟩ :=
    wordGcMoveLoop_thm conf [] pending a n heapMid true limit scanned finalA finalN heapFinal wordFinalA wordFinalPa wordFinalMem wordFinalOk
      freeMid frame wordMem (2 ^ width) curr new dm loopRun rfl boundMid bytesMid lenBound sepLoop steps
      (by simpa [midLen] using limitEq) good loopConcrete freeMidLen.symm
  have rearrange : SetSep.star (SetSep.star (SetSep.star (wordHeap curr heapFinal conf)
      (wordHeap new scanned conf)) (Misc.wordList wordFinalPa freeFinal)) frame =
      SetSep.star (SetSep.star (SetSep.star (wordHeap new scanned conf)
        (Misc.wordList wordFinalPa freeFinal)) frame) (wordHeap curr heapFinal conf) := by ac_rfl
  rw [rearrange] at sepFinal
  have erased := wordHeap_imp_wordListExists heapFinal
    (SetSep.star (SetSep.star (wordHeap new scanned conf) (Misc.wordList wordFinalPa freeFinal)) frame)
    curr conf _ sepFinal
  rw [finalHeapLen, ← wordHeap_heapExpand] at erased
  have rearrangeBack : SetSep.star (SetSep.star (SetSep.star (wordHeap new scanned conf)
      (Misc.wordList wordFinalPa freeFinal)) frame) (wordHeap curr (heapExpand limit) conf) =
      SetSep.star (SetSep.star (SetSep.star (wordHeap new scanned conf)
        (Misc.wordList wordFinalPa freeFinal)) (wordHeap curr (heapExpand limit) conf)) frame := by ac_rfl
  rw [rearrangeBack] at erased
  have freeLength : freeFinal.length = limit - finalA := by omega
  have packed := packFree (wordHeap new scanned conf) (SetSep.star (wordHeap curr (heapExpand limit) conf) frame)
    wordFinalPa freeFinal (limit - finalA) _ freeLength (by
      simpa only [SetSep.starAssoc] using erased)
  rw [← wordHeap_heapExpand] at packed
  refine ⟨?_, c1True, i1Eq, movedEq, ?_⟩
  · rw [wordHeapAppend]
    simpa [SetSep.starAssoc, pa1Eq, wordSemBytesInWord, StackRemove.bytesInWord] using packed
  · simpa [allocEq] using pa1Eq

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
