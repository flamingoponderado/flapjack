import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalRoots
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ListSimulation

/-! Major collector roots stored in word memory. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem starEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]
private instance {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
private instance {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

private theorem wordGenList_zero {width : Nat} [NeZero width] (conf : Config)
    (a i pa ib pb old : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    wordGenGcMoveList conf (a, 0#width, i, pa, ib, pb, old, m, dm) = (a, i, pa, ib, pb, m, true) := by
  rw [wordGenGcMoveList]
  simp

private theorem wordGenList_step {width : Nat} [NeZero width] (conf : Config)
    {l : BitVec width} (hne : l ≠ 0) (a i pa ib pb old : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    wordGenGcMoveList conf (a, l, i, pa, ib, pb, old, m, dm) =
      (let w := m a
       let (w1, i1, pa1, ib1, pb1, m1, c1) := wordGenGcMove conf (w, i, pa, ib, pb, old, m, dm)
       let (a2, i2, pa2, ib2, pb2, m2, c2) :=
         wordGenGcMoveList conf (a + wordSemBytesInWord, l - 1, i1, pa1, ib1, pb1, old, gcUpdate a w1 m1, dm)
       (a2, i2, pa2, ib2, pb2, m2, dm a && (c1 && c2))) := by
  rw [wordGenGcMoveList, ite_eq_right hne]

/-- The copied data, free words and reference objects occupy consecutive
heap regions. Address and stored-word widths are independent, as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_heap_parts_def"
  (words_as_type_indexed_bitvec)]
def wordHeapParts {addressWidth : Nat} {valueWidth : Nat} [NeZero addressWidth] [NeZero valueWidth]
    (conf : Config) (p : BitVec addressWidth)
    (state : GcState (WordLocW valueWidth) (HeapTag × List (WordLocW valueWidth)))
    (xs : List (WordLocW valueWidth)) : ((BitVec addressWidth × WordLocW valueWidth) → Prop) → Prop :=
  SetSep.star (SetSep.star (wordHeap p (state.h1 ++ state.h2) conf)
    (Misc.wordList (p + wordSemBytesInWord * BitVec.ofNat addressWidth (heapLength (state.h1 ++ state.h2))) xs))
    (wordHeap (p + wordSemBytesInWord * BitVec.ofNat addressWidth (heapLength (state.h1 ++ state.h2) + xs.length))
      (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) conf)

/-- Original major-collector in-memory root-list simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_list_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveList_thm {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (roots : List (HeapAddress (WordLocW width))) :
    ∀ (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
      (roots1 : List (HeapAddress (WordLocW width))) (curr pa k k1 i1 pa1 ib1 pb1 : BitVec width)
      (xs : List (WordLocW width)) (memory memory1 : BitVec width → WordLocW width)
      (domain : BitVec width → Bool) (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (c1 : Bool),
      GenGc.gcMoveList genConf state roots = (roots1, state1) → state1.ok = true → state.h2 = [] → state.r4 = [] →
      heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf →
      (∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t) → conf.lenSize + 5 ≤ width →
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr state.heap conf) (Misc.wordList pa xs))
        (Misc.wordList k (roots.map (wordAddr conf)))) frame
        (SetSep.fun2Set (memory, fun address => domain address = true)) →
      wordGenGcMoveList conf (k, BitVec.ofNat width roots.length, BitVec.ofNat width state.a, pa,
        BitVec.ofNat width (state.a + state.n), pa + wordSemBytesInWord * BitVec.ofNat width state.n,
        curr, memory, domain) = (k1, i1, pa1, ib1, pb1, memory1, c1) →
      (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true →
      xs.length = state.n → goodDimindex width → roots.length < 2 ^ width →
      ∃ xs1,
        SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr state1.heap conf)
          (wordHeap pa state1.h2 conf)) (wordHeap pb1 state1.r4 conf)) (Misc.wordList pa1 xs1))
          (Misc.wordList k (roots1.map (wordAddr conf)))) frame
          (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
        heapLength state1.heap = heapLength state.heap ∧ c1 = true ∧ i1 = BitVec.ofNat width state1.a ∧
        ib1 = BitVec.ofNat width (state1.a + state1.n) ∧ state1.n = xs1.length ∧
        state.n = heapLength state1.h2 + state1.n + heapLength state1.r4 ∧
        k1 = k + BitVec.ofNat width roots.length * wordSemBytesInWord ∧
        pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h2) ∧
        pb1 = pa1 + wordSemBytesInWord * BitVec.ofNat width state1.n ∧
        (state1.r4 ++ state1.r3 ++ state1.r2 ++ state1.r1).all (isRefElement genConf.isRef) = true := by
  induction roots with
  | nil =>
    intro state state1 roots1 curr pa k k1 i1 pa1 ib1 pb1 xs memory memory1 domain frame c1
      abstractRun stateOk h2Empty r4Empty heapBound refClass lenBound separated wordRun refs length good rootBound
    simp only [GenGc.gcMoveList, Prod.mk.injEq] at abstractRun
    obtain ⟨rfl, rfl⟩ := abstractRun
    simp only [List.length_nil] at wordRun
    rw [show BitVec.ofNat width 0 = 0#width from rfl, wordGenList_zero] at wordRun
    simp only [Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    refine ⟨xs, ?_, rfl, rfl, rfl, rfl, length.symm, ?_, ?_, ?_, rfl, refs⟩
    · simpa [h2Empty, r4Empty, wordHeap, starEmptyRight] using separated
    · simp [h2Empty, r4Empty, heapLength]
    · simp
    · simp [h2Empty, heapLength]
  | cons root roots ih =>
    intro state state1 roots1 curr pa k k1 i1 pa1 ib1 pb1 xs memory memory1 domain frame c1
      abstractRun stateOk h2Empty r4Empty heapBound refClass lenBound separated wordRun refs length good rootBound
    simp only [GenGc.gcMoveList] at abstractRun
    generalize headRun : GenGc.gcMove genConf state root = headResult at abstractRun
    rcases headResult with ⟨rootMoved, middle⟩
    generalize tailRun : GenGc.gcMoveList genConf middle roots = tailResult at abstractRun
    rcases tailResult with ⟨tailMoved, final⟩
    simp only [Prod.mk.injEq] at abstractRun
    obtain ⟨rfl, rfl⟩ := abstractRun
    have middleOk : middle.ok = true := GenGc.gcMoveList_ok genConf roots tailMoved middle final tailRun stateOk
    have countBound : roots.length + 1 < 2 ^ width := by simpa using rootBound
    have nonzero : BitVec.ofNat width (roots.length + 1) ≠ 0 := by
      intro eq
      have eq' := congrArg BitVec.toNat eq
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound] at eq'
    have minus : BitVec.ofNat width (roots.length + 1) - 1 = BitVec.ofNat width roots.length := by
      rw [BitVec.ofNat_add]
      simp
    have headSep : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (Misc.wordList pa xs))
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
    rw [wordGenList_step conf nonzero, minus, read.1] at wordRun
    generalize wordHead : wordGenGcMove conf (wordAddr conf root, BitVec.ofNat width state.a, pa,
      BitVec.ofNat width (state.a + state.n), pa + wordSemBytesInWord * BitVec.ofNat width state.n,
      curr, memory, domain) = wordHeadResult at wordRun
    rcases wordHeadResult with ⟨wordRoot, headI, headPa, headIb, headPb, headMemory, headOk⟩
    generalize wordTail : wordGenGcMoveList conf (k + wordSemBytesInWord, BitVec.ofNat width roots.length,
      headI, headPa, headIb, headPb, curr, gcUpdate k wordRoot headMemory, domain) = wordTailResult at wordRun
    rcases wordTailResult with ⟨tailK, tailI, tailPa, tailIb, tailPb, tailMemory, tailOk⟩
    simp only [wordHead, wordTail, read.2, Bool.true_and, Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    obtain ⟨freeHead, sepHead, rootEq, heapLen, headOkTrue, headIEq, headIbEq, freeHeadLen,
      spaceEq, headPaEq, headPbEq, headRefs⟩ :=
      wordGenGcMove_thm conf genConf state middle root rootMoved curr pa headI headPa headIb headPb xs memory
        headMemory domain _ wordRoot headOk headRun middleOk h2Empty r4Empty heapBound refClass lenBound
        headSep wordHead length good refs
    obtain ⟨left, right, finalLeft, finalRight, clearRun⟩ :=
      gcMoveList_withNilLemma genConf roots tailMoved middle final tailRun stateOk
    let clearMiddle := { middle with h2 := [], r4 := [] }
    let clearFinal := { final with h2 := left, r4 := right }
    have clearOk : clearFinal.ok = true := stateOk
    have clearRefs : (clearMiddle.r4 ++ clearMiddle.r3 ++ clearMiddle.r2 ++ clearMiddle.r1).all
        (isRefElement genConf.isRef) = true := by
      simp only [List.all_append, Bool.and_eq_true] at headRefs ⊢
      simpa [clearMiddle] using And.intro (And.intro headRefs.1.1.2 headRefs.1.2) headRefs.2
    let tailWords := Misc.wordList (k + StackRemove.bytesInWord width) (roots.map (wordAddr conf))
    let saved := SetSep.star (SetSep.one (k, wordRoot))
      (SetSep.star (wordHeap pa middle.h2 conf) (SetSep.star (wordHeap headPb middle.r4 conf) frame))
    have rearrange : SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr middle.heap conf)
        (wordHeap pa middle.h2 conf)) (wordHeap headPb middle.r4 conf)) (Misc.wordList headPa freeHead))
        (SetSep.star (SetSep.one (k, wordAddr conf root)) (SetSep.star tailWords frame)) =
        SetSep.star (SetSep.one (k, wordAddr conf root))
          (SetSep.star (SetSep.star (SetSep.star (wordHeap curr middle.heap conf) (Misc.wordList headPa freeHead))
            tailWords) (SetSep.star (wordHeap pa middle.h2 conf) (SetSep.star (wordHeap headPb middle.r4 conf) frame))) := by
      ac_rfl
    change (SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr middle.heap conf)
        (wordHeap pa middle.h2 conf)) (wordHeap headPb middle.r4 conf)) (Misc.wordList headPa freeHead))
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
    have tailSep : SetSep.star (SetSep.star (SetSep.star (wordHeap curr clearMiddle.heap conf)
        (Misc.wordList headPa freeHead)) tailWords) saved
        (SetSep.fun2Set (gcUpdate k wordRoot headMemory, fun address => domain address = true)) := by
      rw [updateGraph]
      have order : SetSep.star (SetSep.one (k, wordRoot))
          (SetSep.star (SetSep.star (SetSep.star (wordHeap curr middle.heap conf) (Misc.wordList headPa freeHead))
            tailWords) (SetSep.star (wordHeap pa middle.h2 conf) (SetSep.star (wordHeap headPb middle.r4 conf) frame))) =
          SetSep.star (SetSep.star (SetSep.star (wordHeap curr clearMiddle.heap conf)
            (Misc.wordList headPa freeHead)) tailWords) saved := by
        dsimp [saved, clearMiddle]
        ac_rfl
      rw [← order]
      rw [SetSep.starComm]
      exact written
    have tailWord : wordGenGcMoveList conf (k + StackRemove.bytesInWord width, BitVec.ofNat width roots.length,
        BitVec.ofNat width clearMiddle.a, headPa, BitVec.ofNat width (clearMiddle.a + clearMiddle.n),
        headPa + wordSemBytesInWord * BitVec.ofNat width clearMiddle.n,
        curr, gcUpdate k wordRoot headMemory, domain) = (tailK, tailI, tailPa, tailIb, tailPb, tailMemory, tailOk) := by
      simpa [clearMiddle, headIEq, headIbEq, headPbEq, wordSemBytesInWord, StackRemove.bytesInWord] using wordTail
    have clearBound : heapLength clearMiddle.heap ≤ 2 ^ width / 2 ^ shiftLength conf := by
      simpa [clearMiddle, heapLen] using heapBound
    have tailBound : roots.length < 2 ^ width := by omega
    obtain ⟨freeTail, sepTail, finalHeapLen, tailOkTrue, tailIEq, tailIbEq, freeTailLen,
      tailSpace, tailKEq, tailPaEq, tailPbEq, tailRefs⟩ :=
      ih clearMiddle clearFinal tailMoved curr headPa (k + StackRemove.bytesInWord width) tailK tailI tailPa tailIb tailPb
        freeHead (gcUpdate k wordRoot headMemory) tailMemory domain saved tailOk clearRun clearOk rfl rfl clearBound
        refClass lenBound tailSep tailWord clearRefs freeHeadLen.symm good tailBound
    dsimp only [clearMiddle, clearFinal, tailWords] at sepTail finalHeapLen tailIEq tailIbEq freeTailLen tailSpace tailPaEq tailPbEq tailRefs
    have headPbTail : headPb = tailPb + wordSemBytesInWord * BitVec.ofNat width (heapLength right) := by
      rw [headPbEq, tailPbEq, tailPaEq]
      conv_lhs => rw [tailSpace]
      simp only [BitVec.ofNat_add, BitVec.mul_add]
      ac_rfl
    refine ⟨freeTail, ?_, finalHeapLen.trans heapLen, ?_, tailIEq, tailIbEq, freeTailLen, ?_, ?_, ?_, tailPbEq, ?_⟩
    · rw [finalLeft, finalRight, wordHeapAppend, wordHeapAppend]
      have leftAddr : pa + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength middle.h2) = headPa := by
        simpa [wordSemBytesInWord, StackRemove.bytesInWord] using headPaEq.symm
      have rightAddr : tailPb + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength right) = headPb := by
        simpa [wordSemBytesInWord, StackRemove.bytesInWord] using headPbTail.symm
      rw [leftAddr, rightAddr]
      simp only [List.map_cons, Misc.wordList]
      have order : SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star
          (wordHeap curr final.heap conf)
          (SetSep.star (wordHeap pa middle.h2 conf) (wordHeap headPa left conf)))
          (SetSep.star (wordHeap tailPb right conf) (wordHeap headPb middle.r4 conf)))
          (Misc.wordList tailPa freeTail))
          (SetSep.star (SetSep.one (k, wordAddr conf rootMoved))
            (Misc.wordList (k + StackRemove.bytesInWord width) (tailMoved.map (wordAddr conf))))) frame =
          SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr final.heap conf)
            (wordHeap headPa left conf)) (wordHeap tailPb right conf)) (Misc.wordList tailPa freeTail))
            (Misc.wordList (k + StackRemove.bytesInWord width) (tailMoved.map (wordAddr conf)))) saved := by
        dsimp [saved]
        rw [rootEq]
        ac_rfl
      rw [order]
      exact sepTail
    · simp [headOkTrue, tailOkTrue]
    · rw [finalLeft, finalRight, heapLength_append, heapLength_append]
      omega
    · rw [tailKEq]
      simp only [List.length_cons, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul,
        wordSemBytesInWord, StackRemove.bytesInWord]
      ac_rfl
    · rw [tailPaEq, headPaEq, finalLeft, heapLength_append]
      simp only [BitVec.ofNat_add, BitVec.mul_add]
      ac_rfl
    · rw [finalRight]
      simp only [List.all_append, Bool.and_eq_true] at headRefs tailRefs ⊢
      exact ⟨⟨⟨⟨tailRefs.1.1.1, headRefs.1.1.1⟩, tailRefs.1.1.2⟩, tailRefs.1.2⟩, tailRefs.2⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
