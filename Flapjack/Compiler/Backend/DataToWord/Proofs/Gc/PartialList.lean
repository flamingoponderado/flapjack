import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialRoots

/-! In-memory root-list simulation for partial collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem partialListStarEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]
private instance {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
private instance {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

private theorem partialList_zero {width : Nat} [NeZero width] (conf : Config)
    (a i pa old : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (gs rs : BitVec width) :
    wordGenGcPartialMoveList conf (a, 0#width, i, pa, old, m, dm, gs, rs) = (a, i, pa, m, true) := by
  rw [wordGenGcPartialMoveList]
  simp

/-- Original in-memory pointer-list simulation for partial collection. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_partial_move_list_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveList_thm {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (roots : List (HeapAddress (WordLocW width))) :
    ∀ (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
      (roots1 : List (HeapAddress (WordLocW width)))
      (old current refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (curr pa k k1 i1 pa1 : BitVec width) (xs : List (WordLocW width))
      (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
      (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (c1 : Bool),
      GenGcPartial.gcMoveList genConf state roots = (roots1, state1) → state1.ok = true →
      state.h2 = [] → state.r4 = [] → genConf.limit = heapLength state.heap →
      heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf →
      genConf.genStart ≤ genConf.refsStart → genConf.refsStart ≤ heapLength state.heap →
      heapSegment (genConf.genStart, genConf.refsStart) state.heap = some (old, current, refs) →
      (∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t) →
      heapLength state.heap * (width / 8) < 2 ^ width →
      SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
        (Misc.wordList pa xs)) (Misc.wordList k (roots.map (wordAddr conf)))) frame
        (SetSep.fun2Set (memory, fun address => domain address = true)) →
      wordGenGcPartialMoveList conf (k, BitVec.ofNat width roots.length, BitVec.ofNat width state.a, pa,
        curr, memory, domain, wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
        wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = (k1, i1, pa1, memory1, c1) →
      xs.length = state.n → goodDimindex width → roots.length < 2 ^ width →
      ∃ xs1 current1,
        SetSep.star (SetSep.star (SetSep.star (SetSep.star
          (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current1 conf)
          (wordHeap pa state1.h2 conf)) (Misc.wordList pa1 xs1))
          (Misc.wordList k (roots1.map (wordAddr conf)))) frame
          (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
        heapLength state1.heap = heapLength state.heap ∧
        heapSegment (genConf.genStart, genConf.refsStart) state1.heap = some (old, current1, refs) ∧
        c1 = true ∧ i1 = BitVec.ofNat width state1.a ∧ state1.n = xs1.length ∧
        state.n = heapLength state1.h2 + state1.n + heapLength state1.r4 ∧
        k1 = k + BitVec.ofNat width roots.length * wordSemBytesInWord ∧
        pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h2) := by
  induction roots with
  | nil =>
    intro state state1 roots1 old current refs curr pa k k1 i1 pa1 xs memory memory1 domain frame c1
      abstractRun stateOk h2Empty r4Empty limitEq heapBound ordered refBound segment refClass byteBound separated wordRun length good rootBound
    simp only [GenGcPartial.gcMoveList, Prod.mk.injEq] at abstractRun
    obtain ⟨rfl, rfl⟩ := abstractRun
    simp only [List.length_nil] at wordRun
    rw [show BitVec.ofNat width 0 = 0#width from rfl, partialList_zero] at wordRun
    simp only [Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    refine ⟨xs, current, ?_, rfl, segment, rfl, rfl, length.symm, ?_, ?_, ?_⟩
    · simpa [h2Empty, wordHeap, partialListStarEmptyRight] using separated
    · simp [h2Empty, r4Empty, heapLength]
    · simp
    · simp [h2Empty, heapLength]
  | cons root roots ih =>
    intro state state1 roots1 old current refs curr pa k k1 i1 pa1 xs memory memory1 domain frame c1
      abstractRun stateOk h2Empty r4Empty limitEq heapBound ordered refBound segment refClass byteBound separated wordRun length good rootBound
    simp only [GenGcPartial.gcMoveList] at abstractRun
    generalize headRun : GenGcPartial.gcMove genConf state root = headResult at abstractRun
    obtain ⟨rootMoved, middle⟩ := headResult
    generalize tailRun : GenGcPartial.gcMoveList genConf middle roots = tailResult at abstractRun
    obtain ⟨tailMoved, final⟩ := tailResult
    simp only [Prod.mk.injEq] at abstractRun
    obtain ⟨rfl, rfl⟩ := abstractRun
    have middleOk : middle.ok = true := partialMoveList_okBefore genConf roots middle tailMoved final tailRun stateOk
    have countBound : roots.length + 1 < 2 ^ width := by simpa using rootBound
    have nonzero : BitVec.ofNat width (roots.length + 1) ≠ 0 := by
      intro eq
      have eq' := congrArg BitVec.toNat eq
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound] at eq'
    have minus : BitVec.ofNat width (roots.length + 1) - 1 = BitVec.ofNat width roots.length := by
      rw [BitVec.ofNat_add]
      simp
    have headSep : SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf) (Misc.wordList pa xs))
        (SetSep.star (SetSep.one (k, wordAddr conf root))
          (SetSep.star (Misc.wordList (k + StackRemove.bytesInWord width) (roots.map (wordAddr conf))) frame))
        (SetSep.fun2Set (memory, fun address => domain address = true)) := by
      simpa only [List.map_cons, Misc.wordList, ← SetSep.starAssoc] using separated
    have read : memory k = wordAddr conf root ∧ domain k = true := by
      rcases headSep with ⟨left, right, outer, _, oneAndRest⟩
      rcases oneAndRest with ⟨one, rest, inner, oneEq, _⟩
      have graph : SetSep.fun2Set (memory, fun address => domain address = true) (k, wordAddr conf root) := by
        rw [← outer.1, ← inner.1]
        exact Or.inr (Or.inl (by rw [oneEq]))
      exact (SetSep.fun2SetThm memory _ _ _).mp graph
    simp only [List.length_cons] at wordRun
    rw [wordGenGcPartialMoveList, if_neg nonzero, minus, read.1] at wordRun
    generalize wordHead : wordGenGcPartialMove conf (wordAddr conf root, BitVec.ofNat width state.a, pa,
      curr, memory, domain, wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
      wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = wordHeadResult at wordRun
    obtain ⟨wordRoot, headI, headPa, headMemory, headOk⟩ := wordHeadResult
    generalize wordTail : wordGenGcPartialMoveList conf (k + wordSemBytesInWord, BitVec.ofNat width roots.length,
      headI, headPa, curr, gcUpdate k wordRoot headMemory, domain,
      wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
      wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = wordTailResult at wordRun
    obtain ⟨tailK, tailI, tailPa, tailMemory, tailOk⟩ := wordTailResult
    simp only [wordHead, wordTail, read.2, Bool.true_and, Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    obtain ⟨freeHead, currentHead, sepHead, rootEq, heapLen, headSegment, headOkTrue, headIEq,
        freeHeadLen, spaceEq, headPaEq⟩ :=
      wordGenGcPartialMove_thm conf genConf state middle root rootMoved old current refs curr pa headI headPa xs memory
        headMemory domain _ wordRoot headOk headRun h2Empty r4Empty middleOk limitEq good heapBound ordered refBound
        segment byteBound headSep refClass wordHead length
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
    let tailWords := Misc.wordList (k + StackRemove.bytesInWord width) (roots.map (wordAddr conf))
    let saved := SetSep.star (SetSep.one (k, wordRoot)) (SetSep.star (wordHeap pa middle.h2 conf) frame)
    have rearrange : SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentHead conf)
        (wordHeap pa middle.h2 conf)) (Misc.wordList headPa freeHead))
        (SetSep.star (SetSep.one (k, wordAddr conf root)) (SetSep.star tailWords frame)) =
        SetSep.star (SetSep.one (k, wordAddr conf root))
          (SetSep.star (SetSep.star (SetSep.star
            (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentHead conf)
            (Misc.wordList headPa freeHead)) tailWords) (SetSep.star (wordHeap pa middle.h2 conf) frame)) := by
      ac_rfl
    change (SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentHead conf)
      (wordHeap pa middle.h2 conf)) (Misc.wordList headPa freeHead))
      (SetSep.star (SetSep.one (k, wordAddr conf root)) (SetSep.star tailWords frame))) _ at sepHead
    rw [rearrange] at sepHead
    have written := SetSep.writeFun2Set wordRoot k (wordAddr conf root) _ headMemory
      (fun address => domain address = true) sepHead
    have updateGraph : SetSep.fun2Set (gcUpdate k wordRoot headMemory, fun address => domain address = true) =
        SetSep.fun2Set ((fun key => @ite _ (key = k) (Classical.propDecidable _) wordRoot (headMemory key)),
          fun address => domain address = true) := by
      funext entry
      rcases entry with ⟨key, val⟩
      simp only [SetSep.fun2SetThm, gcUpdate]
      by_cases h : key = k
      · subst key; simp only [ite_true]
      · have h' : k ≠ key := Ne.symm h
        simp only [h, h', ite_false]
    have tailSep : SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentHead conf)
        (Misc.wordList headPa freeHead)) tailWords) saved
        (SetSep.fun2Set (gcUpdate k wordRoot headMemory, fun address => domain address = true)) := by
      rw [updateGraph]
      have order : SetSep.star (SetSep.one (k, wordRoot))
          (SetSep.star (SetSep.star (SetSep.star
            (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentHead conf)
            (Misc.wordList headPa freeHead)) tailWords) (SetSep.star (wordHeap pa middle.h2 conf) frame)) =
          SetSep.star (SetSep.star (SetSep.star
            (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentHead conf)
            (Misc.wordList headPa freeHead)) tailWords) saved := by
        dsimp [saved]
        ac_rfl
      rw [← order, SetSep.starComm]
      exact written
    have tailWord : wordGenGcPartialMoveList conf
        (k + StackRemove.bytesInWord width, BitVec.ofNat width roots.length, BitVec.ofNat width clearMiddle.a,
          headPa, curr, gcUpdate k wordRoot headMemory, domain,
          wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
          wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) =
            (tailK, tailI, tailPa, tailMemory, tailOk) := by
      simpa [clearMiddle, headIEq, wordSemBytesInWord, StackRemove.bytesInWord] using wordTail
    have tailBound : roots.length < 2 ^ width := by omega
    obtain ⟨freeTail, currentTail, sepTail, finalHeapLen, finalSegment, tailOkTrue,
        tailIEq, freeTailLen, tailSpace, tailKEq, tailPaEq⟩ :=
      ih clearMiddle clearFinal tailMoved old currentHead refs curr headPa (k + StackRemove.bytesInWord width)
        tailK tailI tailPa freeHead (gcUpdate k wordRoot headMemory) tailMemory domain saved tailOk
        clearRun clearOk rfl rfl (by simpa [clearMiddle, heapLen] using limitEq)
        (by simpa [clearMiddle, heapLen] using heapBound) ordered (by simpa [clearMiddle, heapLen] using refBound)
        headSegment refClass (by simpa [clearMiddle, heapLen] using byteBound) tailSep tailWord freeHeadLen.symm good tailBound
    dsimp only [clearMiddle, clearFinal, tailWords] at sepTail finalHeapLen finalSegment tailIEq freeTailLen tailSpace tailPaEq
    simp only [rightEmpty, heapLength, List.map_nil, List.sum_nil, Nat.add_zero] at tailSpace
    refine ⟨freeTail, currentTail, ?_, finalHeapLen.trans heapLen, finalSegment, ?_, tailIEq, freeTailLen, ?_, ?_, ?_⟩
    · rw [finalLeft, wordHeapAppend]
      have leftAddr : pa + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength middle.h2) = headPa := by
        simpa [wordSemBytesInWord, StackRemove.bytesInWord] using headPaEq.symm
      rw [leftAddr]
      simp only [List.map_cons, Misc.wordList]
      have order : SetSep.star (SetSep.star (SetSep.star (SetSep.star
          (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentTail conf)
          (SetSep.star (wordHeap pa middle.h2 conf) (wordHeap headPa left conf)))
          (Misc.wordList tailPa freeTail))
          (SetSep.star (SetSep.one (k, wordAddr conf rootMoved))
            (Misc.wordList (k + StackRemove.bytesInWord width) (tailMoved.map (wordAddr conf))))) frame =
          SetSep.star (SetSep.star (SetSep.star (SetSep.star
            (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentTail conf)
            (wordHeap headPa left conf)) (Misc.wordList tailPa freeTail))
            (Misc.wordList (k + StackRemove.bytesInWord width) (tailMoved.map (wordAddr conf)))) saved := by
        dsimp [saved]
        rw [rootEq]
        ac_rfl
      rw [order]
      exact sepTail
    · simp [headOkTrue, tailOkTrue]
    · rw [finalLeft, finalRight, middleR4, rightEmpty]
      simp only [List.append_nil, heapLength_append] at ⊢
      simp only [middleR4, heapLength, List.map_nil, List.sum_nil, Nat.add_zero] at ⊢ spaceEq
      omega
    · rw [tailKEq]
      simp only [List.length_cons, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul,
        wordSemBytesInWord, StackRemove.bytesInWord]
      ac_rfl
    · rw [tailPaEq, headPaEq, finalLeft, heapLength_append]
      simp only [BitVec.ofNat_add, BitVec.mul_add]
      ac_rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
