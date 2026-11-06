import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalForward
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveBlock

/-! Reference object movement in the major collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private instance {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
private instance {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

private theorem starEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]

/-- Reference object case of the major collector move simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMove_ref {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (ptr len : Nat) (value : WordLocW width) (addresses : List (HeapAddress (WordLocW width)))
    (tag : HeapTag) (payload : List (WordLocW width)) (root1 : HeapAddress (WordLocW width))
    (curr pa i1 pa1 ib1 pb1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (w : WordLocW width) (c1 : Bool)
    (found : heapLookup ptr state.heap = some (.dataElement addresses len (tag, payload)))
    (isRef : isMutTag tag)
    (abstractRun : GenGc.gcMove genConf state (.pointer ptr value) = (root1, state1))
    (stateOk : state1.ok = true) (h2Empty : state.h2 = []) (r4Empty : state.r4 = [])
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (lenBound : conf.lenSize + 5 ≤ width)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (Misc.wordList pa xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (wordRun : wordGenGcMove conf (wordAddr conf (.pointer ptr value), BitVec.ofNat width state.a, pa,
      BitVec.ofNat width (state.a + state.n), pa + wordSemBytesInWord * BitVec.ofNat width state.n,
      curr, memory, domain) = (w, i1, pa1, ib1, pb1, memory1, c1))
    (length : xs.length = state.n) (good : goodDimindex width)
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true) :
    ∃ xs1,
      SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr state1.heap conf)
        (wordHeap pa state1.h2 conf)) (wordHeap pb1 state1.r4 conf)) (Misc.wordList pa1 xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      w = wordAddr conf root1 ∧ heapLength state1.heap = heapLength state.heap ∧ c1 = true ∧
      i1 = BitVec.ofNat width state1.a ∧ ib1 = BitVec.ofNat width (state1.a + state1.n) ∧
      state1.n = xs1.length ∧ state.n = heapLength state1.h2 + state1.n + heapLength state1.r4 ∧
      pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h2) ∧
      pb1 = pa1 + wordSemBytesInWord * BitVec.ofNat width state1.n ∧
      (state1.r4 ++ state1.r3 ++ state1.r2 ++ state1.r1).all (isRefElement genConf.isRef) = true := by
  have refTrue : genConf.isRef (tag, payload) = true := (refClass tag payload).mpr isRef
  obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split state.heap ptr _ found
  let remainingCount := state.n - (len + 1)
  let targetIndex := state.a + remainingCount
  have forward (ok : Bool) : gcForwardPtr ptr state.heap (state.a + (state.n - (len + 1))) value ok =
      (before ++ .forwardPointer targetIndex value len :: after, ok) := by
    rw [heapEq, ptrEq]
    exact gcForwardPtr_thm before after addresses len (tag, payload) targetIndex value ok
  simp only [GenGc.gcMove, found, refTrue, ↓reduceIte, forward, Prod.mk.injEq] at abstractRun
  obtain ⟨rfl, rfl⟩ := abstractRun
  simp only [Bool.and_eq_true, decide_eq_true_eq] at stateOk
  obtain ⟨inputOk, space⟩ := stateOk
  obtain ⟨header, words, encoded, wordLen, wordBound, decoded, cell⟩ :=
    wordHeap_dataCell conf before after addresses len tag payload curr pa xs memory domain frame
      (by simpa only [← heapEq] using separated)
  let src := curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr
  have read : memory src = .word header ∧ domain src = true := by
    have graph : SetSep.fun2Set (memory, fun address => domain address = true) (src, .word header) := by
      rcases cell with ⟨sourceAndFrame, free, outSplit, sourceAndFrameAssert, _⟩
      rcases sourceAndFrameAssert with ⟨rest, source, sourceSplit, _, sourceAssert⟩
      have entry := StackRemove.StackHeap.wordListNth
        (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before))
        (.word header :: words) source 0 (by simp) sourceAssert
      rw [← outSplit.1, ← sourceSplit.1]
      apply Or.inl
      apply Or.inr
      simpa [src, ptrEq] using entry
    exact (SetSep.fun2SetThm memory _ _ _).mp graph
  have ptrBound : ptr * 2 ^ shiftLength conf < 2 ^ width := by
    have ptrInHeap := heapLookup_less state.heap ptr (.dataElement addresses len (tag, payload)) found
    have below : ptr < 2 ^ width / 2 ^ shiftLength conf := Nat.lt_of_lt_of_le ptrInHeap heapBound
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right below (Nat.two_pow_pos _)) (Nat.div_mul_le_self _ _)
  have low : getAddr conf ptr value &&& (1 : BitVec width) ≠ 0 := by
    simpa only [BitVec.and_comm] using getAddr_and_one_ne_zero conf ptr value
  have address : ptrToAddr conf curr (getAddr conf ptr value) = src := by
    simpa only [src, wordSemBytesInWord, StackRemove.bytesInWord, BitVec.mul_comm] using
      ptrToAddr_getAddr conf curr ptr value ptrBound
  have notForward : wordSemIsFwdPtr (.word header) = false :=
    wordPayload_not_fwdPtr conf addresses len tag payload header words true encoded
  have headerRef : isRefHeader header = true :=
    (isRefHeader_thm addresses len tag payload conf header words true encoded good lenBound).mpr isRef
  have low' : (1 : BitVec width) &&& getAddr conf ptr value ≠ 0 := by
    simpa [BitVec.and_comm] using low
  let destination := pa + wordSemBytesInWord * BitVec.ofNat width remainingCount
  have nEq : state.n = remainingCount + (len + 1) := by dsimp [remainingCount]; omega
  have indexEq : BitVec.ofNat width (state.a + state.n) - (BitVec.ofNat width words.length + 1) =
      BitVec.ofNat width targetIndex := by
    rw [wordLen]
    conv_lhs => rw [nEq]
    simp [targetIndex, BitVec.ofNat_add, ← BitVec.add_assoc]
  have destEq : pa + wordSemBytesInWord * BitVec.ofNat width state.n -
      (BitVec.ofNat width words.length + 1) * wordSemBytesInWord = destination := by
    rw [wordLen]
    conv_lhs => rw [nEq]
    simp [destination, BitVec.ofNat_add, BitVec.mul_add, BitVec.mul_comm, ← BitVec.add_assoc]
  have remBound : remainingCount ≤ xs.length := by dsimp [remainingCount]; omega
  have takeLen : (xs.take remainingCount).length = remainingCount := by simp [remBound]
  have dropLen : (xs.drop remainingCount).length = len + 1 := by
    simp only [List.length_drop, length]
    dsimp [remainingCount]
    omega
  have splitSep : SetSep.star (SetSep.star (wordHeap curr state.heap conf)
      (Misc.wordList destination (xs.drop remainingCount)))
      (SetSep.star (Misc.wordList pa (xs.take remainingCount)) frame)
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    have splitXs : xs = xs.take remainingCount ++ xs.drop remainingCount := (List.take_append_drop _ _).symm
    rw [splitXs, StackRemove.StackHeap.wordListAppend, takeLen] at separated
    have rearrange : SetSep.star (SetSep.star (wordHeap curr state.heap conf)
        (SetSep.star (Misc.wordList pa (xs.take remainingCount))
          (Misc.wordList destination (xs.drop remainingCount)))) frame =
        SetSep.star (SetSep.star (wordHeap curr state.heap conf)
          (Misc.wordList destination (xs.drop remainingCount)))
          (SetSep.star (Misc.wordList pa (xs.take remainingCount)) frame) := by ac_rfl
    rw [← rearrange]
    simpa [destination, wordSemBytesInWord, StackRemove.bytesInWord] using separated
  simp only [wordAddr, wordGenGcMove, if_neg low', address, read.1, read.2, wordSemTheWord,
    wordSemIsWordLoc, notForward, Bool.false_eq_true, ↓reduceIte, Bool.true_and,
    headerRef, decoded, indexEq, destEq] at wordRun
  generalize copyRun : memcpy (BitVec.ofNat width words.length + 1) src destination memory domain = copyResult at wordRun
  rcases copyResult with ⟨copyEnd, copyMemory, copyOk⟩
  simp only [Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := wordRun
  have copyWordRun : wordGcMove conf (wordAddr conf (.pointer ptr value), BitVec.ofNat width targetIndex,
      destination, curr, memory, domain) =
      (.word (updateAddr conf (BitVec.ofNat width targetIndex) (getAddr conf ptr value)),
        BitVec.ofNat width targetIndex + BitVec.ofNat width words.length + 1,
        copyEnd, gcUpdate src (.word (BitVec.ofNat width targetIndex <<< (2 : Nat))) copyMemory, copyOk) := by
    simp only [wordAddr, wordGcMove, if_neg low, address, read.1, read.2, notForward,
      Bool.false_eq_true, ↓reduceIte, wordSemTheWord, wordSemIsWordLoc, Bool.true_and, decoded, copyRun]
  have copyAbstract : CopyingGc.gcMove (.pointer ptr value, [], targetIndex, len + 1, state.heap, true,
      targetIndex + (len + 1)) =
      (.pointer targetIndex value, [.dataElement addresses len (tag, payload)], targetIndex + len + 1,
        0, before ++ .forwardPointer targetIndex value len :: after, true) := by
    simp [CopyingGc.gcMove, found, forward, targetIndex, remainingCount, Nat.add_assoc]
  obtain ⟨remaining, copiedSep, rootEq, heapLen, ok, indexResult, remainingLen, copyEndEq⟩ :=
    wordGcMove_dataElement conf ptr len value addresses tag payload targetIndex (len + 1) (targetIndex + (len + 1))
      (targetIndex + len + 1) 0 state.heap (before ++ .forwardPointer targetIndex value len :: after)
      [.dataElement addresses len (tag, payload)] curr destination copyEnd
      (BitVec.ofNat width targetIndex + BitVec.ofNat width words.length + 1) (xs.drop remainingCount) memory
      (gcUpdate src (.word (BitVec.ofNat width targetIndex <<< (2 : Nat))) copyMemory) domain
      (SetSep.star (Misc.wordList pa (xs.take remainingCount)) frame) (.pointer targetIndex value)
      (.word (updateAddr conf (BitVec.ofNat width targetIndex) (getAddr conf ptr value)))
      copyOk found copyAbstract heapBound splitSep copyWordRun dropLen
  have remainingEmpty : remaining = [] := List.length_eq_zero_iff.mp remainingLen.symm
  subst remaining
  dsimp only
  refine ⟨xs.take remainingCount, ?_, rootEq, heapLen, ok, rfl, rfl, ?_, ?_, ?_, rfl, ?_⟩
  · simp only [h2Empty, r4Empty, wordHeap, starEmptyRight]
    simp only [Misc.wordList, starEmptyRight] at copiedSep
    have rearrange : SetSep.star (SetSep.star
        (wordHeap curr (before ++ .forwardPointer targetIndex value len :: after) conf)
        (wordHeap destination [.dataElement addresses len (tag, payload)] conf))
        (SetSep.star (Misc.wordList pa (xs.take remainingCount)) frame) =
        SetSep.star (SetSep.star (SetSep.star
          (wordHeap curr (before ++ .forwardPointer targetIndex value len :: after) conf)
          (wordHeap destination [.dataElement addresses len (tag, payload)] conf))
          (Misc.wordList pa (xs.take remainingCount))) frame := by ac_rfl
    rw [rearrange] at copiedSep
    simpa [wordHeap, starEmptyRight] using copiedSep
  · simpa [remainingCount] using takeLen.symm
  · simp only [h2Empty, r4Empty, heapLength, List.map_nil, List.map_cons, List.sum_nil,
      List.sum_cons, elLength, Nat.zero_add]
    omega
  · simp [h2Empty, heapLength]
  · simpa [isRefElement, refTrue] using refs

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
