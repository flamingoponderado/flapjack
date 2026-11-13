module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalForward
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveBlock

@[expose] public section

/-! Non-reference object movement in the major collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem starEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]

/-- Non-reference object case of the major collector move simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMove_nonRef {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (ptr len : Nat) (value : WordLocW width) (addresses : List (HeapAddress (WordLocW width)))
    (tag : HeapTag) (payload : List (WordLocW width)) (root1 : HeapAddress (WordLocW width))
    (curr pa i1 pa1 ib1 pb1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (w : WordLocW width) (c1 : Bool)
    (found : heapLookup ptr state.heap = some (.dataElement addresses len (tag, payload)))
    (nonRef : ¬ isMutTag tag)
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
  have refFalse : genConf.isRef (tag, payload) = false := by
    cases h : genConf.isRef (tag, payload) with
    | false => rfl
    | true => exact False.elim (nonRef ((refClass tag payload).mp h))
  obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split state.heap ptr _ found
  have forward (ok : Bool) : gcForwardPtr ptr state.heap state.a value ok =
      (before ++ .forwardPointer state.a value len :: after, ok) := by
    rw [heapEq, ptrEq]
    exact gcForwardPtr_thm before after addresses len (tag, payload) state.a value ok
  simp only [GenGc.gcMove, found, refFalse, Bool.false_eq_true, ↓reduceIte, forward,
    Prod.mk.injEq] at abstractRun
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
  have headerNotRef : isRefHeader header = false := by
    cases h : isRefHeader header with
    | false => rfl
    | true => exact False.elim (nonRef ((isRefHeader_thm addresses len tag payload conf header words true
        encoded good lenBound).mp h))
  have low' : (1 : BitVec width) &&& getAddr conf ptr value ≠ 0 := by
    simpa [BitVec.and_comm] using low
  simp only [wordAddr, wordGenGcMove, ite_eq_right low', address, read.1, read.2, wordSemTheWord,
    wordSemIsWordLoc, notForward, Bool.false_eq_true, ↓reduceIte, Bool.true_and,
    headerNotRef, decoded] at wordRun
  generalize copyRun : memcpy (BitVec.ofNat width words.length + 1) src pa memory domain = copyResult at wordRun
  rcases copyResult with ⟨copyEnd, copyMemory, copyOk⟩
  simp only [Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := wordRun
  have copyWordRun : wordGcMove conf (wordAddr conf (.pointer ptr value), BitVec.ofNat width state.a,
      pa, curr, memory, domain) =
      (.word (updateAddr conf (BitVec.ofNat width state.a) (getAddr conf ptr value)),
        BitVec.ofNat width state.a + BitVec.ofNat width words.length + 1,
        copyEnd, gcUpdate src (.word (BitVec.ofNat width state.a <<< (2 : Nat))) copyMemory, copyOk) := by
    simp only [wordAddr, wordGcMove, ite_eq_right low, address, read.1, read.2, notForward,
      Bool.false_eq_true, ↓reduceIte, wordSemTheWord, wordSemIsWordLoc, Bool.true_and, decoded, copyRun]
  have copyAbstract : CopyingGc.gcMove (.pointer ptr value, [], state.a, state.n, state.heap, true,
      state.a + state.n) =
      (.pointer state.a value, [.dataElement addresses len (tag, payload)], state.a + len + 1,
        state.n - (len + 1), before ++ .forwardPointer state.a value len :: after, true) := by
    simp [CopyingGc.gcMove, found, forward, space, Nat.add_assoc]
  obtain ⟨remaining, copiedSep, rootEq, heapLen, ok, indexEq, remainingLen, paEq⟩ :=
    wordGcMove_dataElement conf ptr len value addresses tag payload state.a state.n (state.a + state.n)
      (state.a + len + 1) (state.n - (len + 1)) state.heap
      (before ++ .forwardPointer state.a value len :: after) [.dataElement addresses len (tag, payload)]
      curr pa copyEnd (BitVec.ofNat width state.a + BitVec.ofNat width words.length + 1) xs memory
      (gcUpdate src (.word (BitVec.ofNat width state.a <<< (2 : Nat))) copyMemory) domain frame
      (.pointer state.a value) (.word (updateAddr conf (BitVec.ofNat width state.a) (getAddr conf ptr value)))
      copyOk found copyAbstract heapBound separated copyWordRun length
  dsimp only
  refine ⟨remaining, ?_, rootEq, heapLen, ok, indexEq, ?_, remainingLen, ?_, ?_, ?_, refs⟩
  · simpa [h2Empty, r4Empty, wordHeap, starEmptyRight] using copiedSep
  · congr 1
    omega
  · simp only [h2Empty, r4Empty, List.nil_append, heapLength, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, elLength]
    omega
  · simpa [h2Empty] using paEq
  · rw [paEq]
    simp only [heapLength, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, elLength]
    have eq : len + 1 + (state.n - (len + 1)) = state.n := by omega
    conv_lhs => rw [← eq, BitVec.ofNat_add, BitVec.mul_add]
    ac_rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
