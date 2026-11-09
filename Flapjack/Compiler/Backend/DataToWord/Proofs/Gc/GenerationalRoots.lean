module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalMove
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalAccumulator
public import Flapjack.Compiler.Backend.GenGc.Proofs.Progress

@[expose] public section

/-! Root-list simulation for major generational collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem starEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]

instance generationalRootsInst1 {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
instance generationalRootsInst2 {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

/-- Full root-list simulation for the major collector. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_roots_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveRoots_thm {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (curr pa i1 pa1 ib1 pb1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (w : List (WordLocW width)) (c1 : Bool)
    (abstractRun : GenGc.gcMoveList genConf state roots = (roots1, state1))
    (stateOk : state1.ok = true) (h2Empty : state.h2 = []) (r4Empty : state.r4 = [])
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (lenBound : conf.lenSize + 5 ≤ width)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (Misc.wordList pa xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (wordRun : wordGenGcMoveRoots conf (roots.map (wordAddr conf), BitVec.ofNat width state.a, pa,
      BitVec.ofNat width (state.a + state.n), pa + wordSemBytesInWord * BitVec.ofNat width state.n,
      curr, memory, domain) = (w, i1, pa1, ib1, pb1, memory1, c1))
    (length : xs.length = state.n) (good : goodDimindex width)
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true) :
    ∃ xs1,
      SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr state1.heap conf)
        (wordHeap pa state1.h2 conf)) (wordHeap pb1 state1.r4 conf)) (Misc.wordList pa1 xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      w = roots1.map (wordAddr conf) ∧ heapLength state1.heap = heapLength state.heap ∧ c1 = true ∧
      i1 = BitVec.ofNat width state1.a ∧ ib1 = BitVec.ofNat width (state1.a + state1.n) ∧
      state1.n = xs1.length ∧ state.n = heapLength state1.h2 + state1.n + heapLength state1.r4 ∧
      pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h2) ∧
      pb1 = pa1 + wordSemBytesInWord * BitVec.ofNat width state1.n ∧
      (state1.r4 ++ state1.r3 ++ state1.r2 ++ state1.r1).all (isRefElement genConf.isRef) = true := by
  induction roots generalizing state state1 roots1 pa i1 pa1 ib1 pb1 xs memory memory1 w c1 frame with
  | nil =>
    simp only [GenGc.gcMoveList, Prod.mk.injEq] at abstractRun
    obtain ⟨rfl, rfl⟩ := abstractRun
    simp only [List.map_nil, wordGenGcMoveRoots, Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    refine ⟨xs, ?_, rfl, rfl, rfl, rfl, rfl, length.symm, ?_, ?_, rfl, refs⟩
    · simpa [h2Empty, r4Empty, wordHeap, starEmptyRight] using separated
    · simp [h2Empty, r4Empty, heapLength]
    · simp [h2Empty, heapLength]
  | cons root roots ih =>
    simp only [GenGc.gcMoveList] at abstractRun
    generalize headRun : GenGc.gcMove genConf state root = headResult at abstractRun
    rcases headResult with ⟨rootMoved, middle⟩
    generalize tailRun : GenGc.gcMoveList genConf middle roots = tailResult at abstractRun
    rcases tailResult with ⟨tailMoved, final⟩
    simp only [Prod.mk.injEq] at abstractRun
    obtain ⟨rfl, rfl⟩ := abstractRun
    have middleOk : middle.ok = true := GenGc.gcMoveList_ok genConf roots tailMoved middle final tailRun stateOk
    simp only [List.map_cons, wordGenGcMoveRoots] at wordRun
    generalize wordHead : wordGenGcMove conf (wordAddr conf root, BitVec.ofNat width state.a, pa,
      BitVec.ofNat width (state.a + state.n), pa + wordSemBytesInWord * BitVec.ofNat width state.n,
      curr, memory, domain) = wordHeadResult at wordRun
    rcases wordHeadResult with ⟨wordRoot, headI, headPa, headIb, headPb, headMemory, headOk⟩
    generalize wordTail : wordGenGcMoveRoots conf (roots.map (wordAddr conf), headI, headPa, headIb,
      headPb, curr, headMemory, domain) = wordTailResult at wordRun
    rcases wordTailResult with ⟨wordRoots, tailI, tailPa, tailIb, tailPb, tailMemory, tailOk⟩
    simp only [Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    obtain ⟨freeHead, sepHead, rootEq, heapLen, headOkTrue, headIEq, headIbEq, freeHeadLen,
      spaceEq, headPaEq, headPbEq, headRefs⟩ :=
      wordGenGcMove_thm conf genConf state middle root rootMoved curr pa headI headPa headIb headPb xs memory
        headMemory domain frame wordRoot headOk headRun middleOk h2Empty r4Empty heapBound refClass lenBound
        separated wordHead length good refs
    obtain ⟨left, right, finalLeft, finalRight, clearRun⟩ :=
      gcMoveList_withNilLemma genConf roots tailMoved middle final tailRun stateOk
    let clearMiddle := { middle with h2 := [], r4 := [] }
    let clearFinal := { final with h2 := left, r4 := right }
    have clearOk : clearFinal.ok = true := stateOk
    have clearRefs : (clearMiddle.r4 ++ clearMiddle.r3 ++ clearMiddle.r2 ++ clearMiddle.r1).all
        (isRefElement genConf.isRef) = true := by
      simp only [List.all_append, Bool.and_eq_true] at headRefs ⊢
      simpa [clearMiddle] using And.intro (And.intro headRefs.1.1.2 headRefs.1.2) headRefs.2
    let saved := SetSep.star (wordHeap pa middle.h2 conf) (SetSep.star (wordHeap headPb middle.r4 conf) frame)
    have tailSep : SetSep.star (SetSep.star (wordHeap curr clearMiddle.heap conf) (Misc.wordList headPa freeHead)) saved
        (SetSep.fun2Set (headMemory, fun address => domain address = true)) := by
      have rearrange : SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr middle.heap conf)
          (wordHeap pa middle.h2 conf)) (wordHeap headPb middle.r4 conf)) (Misc.wordList headPa freeHead)) frame =
          SetSep.star (SetSep.star (wordHeap curr middle.heap conf) (Misc.wordList headPa freeHead)) saved := by
        dsimp [saved]
        ac_rfl
      rw [rearrange] at sepHead
      exact sepHead
    have tailWord : wordGenGcMoveRoots conf (roots.map (wordAddr conf), BitVec.ofNat width clearMiddle.a, headPa,
        BitVec.ofNat width (clearMiddle.a + clearMiddle.n), headPa + wordSemBytesInWord * BitVec.ofNat width clearMiddle.n,
        curr, headMemory, domain) = (wordRoots, tailI, tailPa, tailIb, tailPb, tailMemory, tailOk) := by
      simpa [clearMiddle, headIEq, headIbEq, headPbEq] using wordTail
    have clearBound : heapLength clearMiddle.heap ≤ 2 ^ width / 2 ^ shiftLength conf := by
      simpa [clearMiddle, heapLen] using heapBound
    obtain ⟨freeTail, sepTail, rootsEq, finalHeapLen, tailOkTrue, tailIEq, tailIbEq, freeTailLen,
      tailSpace, tailPaEq, tailPbEq, tailRefs⟩ :=
      ih clearMiddle clearFinal tailMoved headPa tailI tailPa tailIb tailPb freeHead headMemory tailMemory saved wordRoots tailOk
        clearRun clearOk rfl rfl clearBound tailSep tailWord freeHeadLen.symm clearRefs
    dsimp only [clearMiddle, clearFinal] at sepTail finalHeapLen tailIEq tailIbEq freeTailLen tailSpace tailPaEq tailPbEq tailRefs
    have headPbTail : headPb = tailPb + wordSemBytesInWord * BitVec.ofNat width (heapLength right) := by
      rw [headPbEq, tailPbEq, tailPaEq]
      conv_lhs => rw [tailSpace]
      simp only [BitVec.ofNat_add, BitVec.mul_add]
      ac_rfl
    refine ⟨freeTail, ?_, ?_, finalHeapLen.trans heapLen, ?_, tailIEq, tailIbEq, freeTailLen,
      ?_, ?_, tailPbEq, ?_⟩
    · rw [finalLeft, finalRight, wordHeapAppend, wordHeapAppend]
      have leftAddr : pa + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength middle.h2) = headPa := by
        simpa [wordSemBytesInWord, StackRemove.bytesInWord] using headPaEq.symm
      have rightAddr : tailPb + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength right) = headPb := by
        simpa [wordSemBytesInWord, StackRemove.bytesInWord] using headPbTail.symm
      rw [leftAddr, rightAddr]
      have rearrange : SetSep.star (SetSep.star (SetSep.star
          (SetSep.star (wordHeap curr final.heap conf)
            (SetSep.star (wordHeap pa middle.h2 conf) (wordHeap headPa left conf)))
          (SetSep.star (wordHeap tailPb right conf) (wordHeap headPb middle.r4 conf)))
          (Misc.wordList tailPa freeTail)) frame =
          SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr final.heap conf)
            (wordHeap headPa left conf)) (wordHeap tailPb right conf)) (Misc.wordList tailPa freeTail)) saved := by
        dsimp [saved]
        ac_rfl
      rw [rearrange]
      exact sepTail
    · simp [rootEq, rootsEq]
    · simp [headOkTrue, tailOkTrue]
    · rw [finalLeft, finalRight, heapLength_append, heapLength_append]
      omega
    · rw [tailPaEq, headPaEq, finalLeft, heapLength_append]
      simp only [BitVec.ofNat_add, BitVec.mul_add]
      ac_rfl
    · rw [finalRight]
      simp only [List.all_append, Bool.and_eq_true] at headRefs tailRefs ⊢
      exact ⟨⟨⟨⟨tailRefs.1.1.1, headRefs.1.1.1⟩, tailRefs.1.1.2⟩, tailRefs.1.2⟩, tailRefs.2⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
