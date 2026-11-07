import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Generational
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveForward

/-! Forwarding-pointer case of the major collector simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem starEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]

private theorem shiftedForward_isForward {width : Nat} [NeZero width] (value : BitVec width) :
    wordSemIsFwdPtr (.word (value <<< (2 : Nat))) = true := by
  simp only [wordSemIsFwdPtr, decide_eq_true_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  by_cases h : i < 2
  · simp [h]
  · have h' : 2 ≤ i := by omega
    have pow : 2 ^ 2 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) h'
    have bit : (3 : Nat).testBit i = false := Nat.testBit_lt_two_pow (by omega)
    simp [h, BitVec.getLsbD_ofNat, bit]


/-- Forwarding-pointer case; the lookup selects the corresponding original case. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMove_forward {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (ptr forwarded len : Nat) (value oldValue : WordLocW width) (root1 : HeapAddress (WordLocW width))
    (curr pa i1 pa1 ib1 pb1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (w : WordLocW width) (c1 : Bool)
    (found : heapLookup ptr state.heap = some (.forwardPointer forwarded oldValue len))
    (abstractRun : GenGc.gcMove genConf state (.pointer ptr value) = (root1, state1))
    (stateOk : state1.ok = true) (h2Empty : state.h2 = []) (r4Empty : state.r4 = [])
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (_refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (_lenBound : conf.lenSize + 5 ≤ width)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (Misc.wordList pa xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (wordRun : wordGenGcMove conf (wordAddr conf (.pointer ptr value), BitVec.ofNat width state.a, pa,
      BitVec.ofNat width (state.a + state.n), pa + wordSemBytesInWord * BitVec.ofNat width state.n,
      curr, memory, domain) = (w, i1, pa1, ib1, pb1, memory1, c1))
    (length : xs.length = state.n) (_good : goodDimindex width)
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
  have bound : ptr * 2 ^ shiftLength conf < 2 ^ width := by
    have ptrBound := heapLookup_less state.heap ptr (.forwardPointer forwarded oldValue len) found
    have below : ptr < 2 ^ width / 2 ^ shiftLength conf := Nat.lt_of_lt_of_le ptrBound heapBound
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right below (Nat.two_pow_pos _)) (Nat.div_mul_le_self _ _)
  have read : memory (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr) =
      .word (BitVec.ofNat width forwarded <<< (2 : Nat)) ∧
      domain (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr) = true := by
    have graph : SetSep.fun2Set (memory, fun address => domain address = true)
        (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
          .word (BitVec.ofNat width forwarded <<< (2 : Nat))) := by
      obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split state.heap ptr _ found
      rcases separated with ⟨heapAndList, rest, outSplit, heapAndListAssert, _⟩
      rcases heapAndListAssert with ⟨heapPart, listPart, heapSplit, heapAssert, _⟩
      rw [heapEq, wordHeapAppend] at heapAssert
      rcases heapAssert with ⟨pre, post, preSplit, _, postAssert⟩
      change SetSep.star (wordEl _ (.forwardPointer forwarded oldValue len) conf)
        (wordHeap _ after conf) post at postAssert
      rcases postAssert with ⟨cell, suffix, postSplit, cellAssert, _⟩
      simp only [wordEl] at cellAssert
      rcases cellAssert with ⟨singleton, restCell, cellSplit, singletonEq, _⟩
      rw [ptrEq, ← outSplit.1, ← heapSplit.1, ← preSplit.1, ← postSplit.1, ← cellSplit.1]
      exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (by rw [singletonEq])))))
    exact (SetSep.fun2SetThm memory _ _ _).mp graph
  have low : getAddr conf ptr value &&& (1 : BitVec width) ≠ 0 := by
    simpa only [BitVec.and_comm] using getAddr_and_one_ne_zero conf ptr value
  have addr : ptrToAddr conf curr (getAddr conf ptr value) =
      curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr := by
    simpa only [wordSemBytesInWord, StackRemove.bytesInWord, BitVec.mul_comm] using
      ptrToAddr_getAddr conf curr ptr value bound
  simp only [GenGc.gcMove, found, Prod.mk.injEq] at abstractRun
  obtain ⟨rfl, rfl⟩ := abstractRun
  have low' : (1 : BitVec width) &&& getAddr conf ptr value ≠ 0 := by
    simpa [BitVec.and_comm] using low
  simp only [wordAddr, wordGenGcMove, ite_eq_right low', addr, read.1, read.2,
    shiftedForward_isForward, ↓reduceIte, wordSemTheWord, wordSemIsWordLoc,
    Bool.true_and, Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := wordRun
  refine ⟨xs, ?_, ?_, rfl, rfl, rfl, rfl, length.symm, ?_, ?_, rfl, refs⟩
  · simpa [h2Empty, r4Empty, wordHeap, starEmptyRight] using separated
  · simp only [wordAddr, updateAddr_forward]
  · simp [h2Empty, r4Empty, heapLength]
  · simp [h2Empty, heapLength]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
