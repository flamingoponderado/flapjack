import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialMove
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialAccumulator

/-! Root-list simulation for the partial generational collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem partialRootsStarEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]

private instance {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
private instance {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

/-- Original partial-collector root-list simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_partial_move_roots_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveRoots_thm {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (old current refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa i1 pa1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (w : List (WordLocW width)) (c1 : Bool)
    (abstractRun : GenGcPartial.gcMoveList genConf state roots = (roots1, state1))
    (stateOk : state1.ok = true) (h2Empty : state.h2 = []) (r4Empty : state.r4 = [])
    (limitEq : genConf.limit = heapLength state.heap)
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (ordered : genConf.genStart ≤ genConf.refsStart) (refBound : genConf.refsStart ≤ heapLength state.heap)
    (segment : heapSegment (genConf.genStart, genConf.refsStart) state.heap = some (old, current, refs))
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (byteBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (separated : SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (Misc.wordList pa xs)) frame (SetSep.fun2Set (memory, fun address => domain address = true)))
    (wordRun : wordGenGcPartialMoveRoots conf
      (roots.map (wordAddr conf), BitVec.ofNat width state.a, pa, curr, memory, domain,
       wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
       wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = (w, i1, pa1, memory1, c1))
    (length : xs.length = state.n) (good : goodDimindex width) :
    ∃ xs1 current1,
      SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current1 conf)
        (wordHeap pa state1.h2 conf)) (Misc.wordList pa1 xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      w = roots1.map (wordAddr conf) ∧ heapLength state1.heap = heapLength state.heap ∧
      heapSegment (genConf.genStart, genConf.refsStart) state1.heap = some (old, current1, refs) ∧
      c1 = true ∧ i1 = BitVec.ofNat width state1.a ∧ state1.n = xs1.length ∧
      state.n = heapLength state1.h2 + state1.n + heapLength state1.r4 ∧
      pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h2) := by
  induction roots generalizing state state1 roots1 pa i1 pa1 xs memory memory1 w c1 frame current with
  | nil =>
    simp only [GenGcPartial.gcMoveList, Prod.mk.injEq] at abstractRun
    obtain ⟨rfl, rfl⟩ := abstractRun
    simp only [List.map_nil, wordGenGcPartialMoveRoots, Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    refine ⟨xs, current, ?_, rfl, rfl, segment, rfl, rfl, length.symm, ?_, ?_⟩
    · simpa [h2Empty, wordHeap, partialRootsStarEmptyRight] using separated
    · simp [h2Empty, r4Empty, heapLength]
    · simp [h2Empty, heapLength]
  | cons root roots ih =>
    simp only [GenGcPartial.gcMoveList] at abstractRun
    generalize headRun : GenGcPartial.gcMove genConf state root = headResult at abstractRun
    obtain ⟨rootMoved, middle⟩ := headResult
    generalize tailRun : GenGcPartial.gcMoveList genConf middle roots = tailResult at abstractRun
    obtain ⟨tailMoved, final⟩ := tailResult
    simp only [Prod.mk.injEq] at abstractRun
    obtain ⟨rfl, rfl⟩ := abstractRun
    have middleOk : middle.ok = true := partialMoveList_okBefore genConf roots middle tailMoved final tailRun stateOk
    simp only [List.map_cons, wordGenGcPartialMoveRoots] at wordRun
    generalize wordHead : wordGenGcPartialMove conf (wordAddr conf root, BitVec.ofNat width state.a, pa,
      curr, memory, domain, wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
      wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = wordHeadResult at wordRun
    obtain ⟨wordRoot, headI, headPa, headMemory, headOk⟩ := wordHeadResult
    generalize wordTail : wordGenGcPartialMoveRoots conf (roots.map (wordAddr conf), headI, headPa,
      curr, headMemory, domain, wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
      wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = wordTailResult at wordRun
    obtain ⟨wordRoots, tailI, tailPa, tailMemory, tailOk⟩ := wordTailResult
    simp only [Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    obtain ⟨freeHead, currentHead, sepHead, rootEq, heapLen, headSegment, headOkTrue, headIEq,
        freeHeadLen, spaceEq, headPaEq⟩ :=
      wordGenGcPartialMove_thm conf genConf state middle root rootMoved old current refs curr pa headI headPa xs
        memory headMemory domain frame wordRoot headOk headRun h2Empty r4Empty middleOk limitEq good heapBound
        ordered refBound segment byteBound separated refClass wordHead length
    have middleR4 : middle.r4 = [] := by
      have same := GenGcPartial.gcMove_r4 genConf state root
      rw [headRun] at same
      exact same.trans r4Empty
    obtain ⟨left, right, finalLeft, finalRight, clearRun⟩ :=
      partialMoveList_withNilLemma genConf roots middle tailMoved final tailRun stateOk
    let clearMiddle := { middle with h2 := [], r4 := [] }
    let clearFinal := { final with h2 := left, r4 := right }
    have clearOk : clearFinal.ok = true := stateOk
    have rightEmpty : right = [] := by
      have same := GenGcPartial.gcMoveList_r4 genConf clearMiddle roots
      change GenGcPartial.gcMoveList genConf clearMiddle roots = (tailMoved, clearFinal) at clearRun
      rw [clearRun] at same
      simpa [clearMiddle, clearFinal] using same
    let saved := SetSep.star (wordHeap pa middle.h2 conf) frame
    have tailSep : SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentHead conf)
        (Misc.wordList headPa freeHead)) saved (SetSep.fun2Set (headMemory, fun address => domain address = true)) := by
      have rearrange : SetSep.star (SetSep.star (SetSep.star
          (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentHead conf)
          (wordHeap pa middle.h2 conf)) (Misc.wordList headPa freeHead)) frame =
          SetSep.star (SetSep.star
            (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentHead conf)
            (Misc.wordList headPa freeHead)) saved := by
        dsimp [saved]
        ac_rfl
      rw [rearrange] at sepHead
      exact sepHead
    have tailWord : wordGenGcPartialMoveRoots conf
        (roots.map (wordAddr conf), BitVec.ofNat width clearMiddle.a, headPa, curr, headMemory, domain,
          wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
          wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) =
            (wordRoots, tailI, tailPa, tailMemory, tailOk) := by
      simpa [clearMiddle, headIEq] using wordTail
    obtain ⟨freeTail, currentTail, sepTail, rootsEq, finalHeapLen, finalSegment, tailOkTrue,
        tailIEq, freeTailLen, tailSpace, tailPaEq⟩ :=
      ih clearMiddle clearFinal tailMoved currentHead headPa tailI tailPa freeHead headMemory tailMemory saved wordRoots tailOk
        clearRun clearOk rfl rfl (by simpa [clearMiddle, heapLen] using limitEq)
        (by simpa [clearMiddle, heapLen] using heapBound) (by simpa [clearMiddle, heapLen] using refBound)
        headSegment (by simpa [clearMiddle, heapLen] using byteBound) tailSep tailWord freeHeadLen.symm
    dsimp only [clearMiddle, clearFinal] at sepTail finalHeapLen finalSegment tailIEq freeTailLen tailSpace tailPaEq
    simp only [rightEmpty, heapLength, List.map_nil, List.sum_nil, Nat.add_zero] at tailSpace
    refine ⟨freeTail, currentTail, ?_, ?_, finalHeapLen.trans heapLen, finalSegment,
      ?_, tailIEq, freeTailLen, ?_, ?_⟩
    · rw [finalLeft, wordHeapAppend]
      have leftAddr : pa + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength middle.h2) = headPa := by
        simpa [wordSemBytesInWord, StackRemove.bytesInWord] using headPaEq.symm
      rw [leftAddr]
      have rearrange : SetSep.star (SetSep.star (SetSep.star
          (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentTail conf)
          (SetSep.star (wordHeap pa middle.h2 conf) (wordHeap headPa left conf)))
          (Misc.wordList tailPa freeTail)) frame =
          SetSep.star (SetSep.star (SetSep.star
            (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentTail conf)
            (wordHeap headPa left conf)) (Misc.wordList tailPa freeTail)) saved := by
        dsimp [saved]
        ac_rfl
      rw [rearrange]
      exact sepTail
    · simp [rootEq, rootsEq]
    · simp [headOkTrue, tailOkTrue]
    · rw [finalLeft, finalRight, middleR4, rightEmpty]
      simp only [List.append_nil, heapLength_append] at ⊢
      simp only [middleR4, heapLength, List.map_nil, List.sum_nil, Nat.add_zero] at ⊢ spaceEq
      omega
    · rw [tailPaEq, headPaEq, finalLeft, heapLength_append]
      simp only [BitVec.ofNat_add, BitVec.mul_add]
      ac_rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
