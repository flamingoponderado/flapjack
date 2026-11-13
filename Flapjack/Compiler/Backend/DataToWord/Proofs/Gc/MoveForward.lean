module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PointerAddress
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveData
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader

@[expose] public section

/-! Forwarding-pointer case of the copying collector simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem starEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]

/-- Shifting a value left by two sets the forward-pointer marker. Shared by
the copying, major and partial collector move proofs; no separately named HOL
original. -/
theorem shiftedForward_isForward {width : Nat} [NeZero width] (value : BitVec width) :
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

/-- Bit-vector factoring used by the collector move cases; this helper has no
standalone HOL declaration. -/
theorem updateAddr_forward {width : Nat} [NeZero width] (conf : Config)
    (index forwarded : Nat) (value : WordLocW width) :
    updateAddr conf ((BitVec.ofNat width forwarded <<< (2 : Nat)) >>> (2 : Nat))
      (getAddr conf index value) = getAddr conf forwarded value := by
  have smallPos : 0 < smallShiftLength conf := by simp [smallShiftLength]
  have smallLe : smallShiftLength conf ≤ shiftLength conf := by simp [smallShiftLength, shiftLength]
  have shiftTwo : 2 ≤ shiftLength conf := by simp [shiftLength]; omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have repr (x : BitVec width) : x.toNat.testBit i = x.getLsbD i := by
    rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_eq_testBit_toNat]
  have lowOff (h : smallShiftLength conf ≤ i) : (getLowerBits conf value).getLsbD i = false := by
    cases value with
    | word w =>
      simp only [getLowerBits, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_extractLsb', Nat.zero_add]
      have nz : i ≠ 0 := by omega
      have notSmall : ¬ i < smallShiftLength conf := by omega
      simp [notSmall, nz]
    | loc a b =>
      have nz : i ≠ 0 := by omega
      simp [getLowerBits, nz]
  simp only [updateAddr, gcWordBitsLow, getAddr, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and]
  rw [repr]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have pred : smallShiftLength conf - 1 + 1 = smallShiftLength conf := by omega
  simp only [pred]
  by_cases low : i < smallShiftLength conf
  · have notShift : i < shiftLength conf := by omega
    simp [low, notShift]
  · have beyond : smallShiftLength conf ≤ i := by omega
    rw [lowOff beyond]
    by_cases inShift : i < shiftLength conf
    · simp [low, inShift]
    · have twoBound : 2 + (i - shiftLength conf) < width := by omega
      have subBound : i - shiftLength conf < width := by omega
      have twoNot : ¬ 2 + (i - shiftLength conf) < 2 := by omega
      simp [low, inShift, twoBound, subBound, twoNot, hi]

/-- The forwarding-pointer branch of the collector move simulation. The
lookup fixes the constructor examined by the original proof; all original
execution, heap, separation, and output conditions are retained. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_move_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGcMove_forward {width : Nat} [NeZero width] (conf : Config)
    (ptr forwarded len : Nat) (value oldValue : WordLocW width) (a n limit a1 n1 : Nat)
    (heap heap1 h1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa pa1 i1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (x1 : HeapAddress (WordLocW width)) (w : WordLocW width) (c1 : Bool)
    (found : heapLookup ptr heap = some (.forwardPointer forwarded oldValue len))
    (abstractRun : CopyingGc.gcMove (.pointer ptr value, [], a, n, heap, true, limit) =
      (x1, h1, a1, n1, heap1, true))
    (heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (separated : SetSep.star (SetSep.star (wordHeap curr heap conf) (Misc.wordList pa xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (wordRun : wordGcMove conf (wordAddr conf (.pointer ptr value), BitVec.ofNat width a, pa,
      curr, memory, domain) = (w, i1, pa1, memory1, c1)) (length : xs.length = n) :
    ∃ xs1,
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap1 conf) (wordHeap pa h1 conf))
        (Misc.wordList pa1 xs1)) frame (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      w = wordAddr conf x1 ∧ heapLength heap1 = heapLength heap ∧ c1 = true ∧
      i1 = BitVec.ofNat width a1 ∧ n1 = xs1.length ∧
      pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength h1) := by
  have bound : ptr * 2 ^ shiftLength conf < 2 ^ width := by
    have ptrBound := heapLookup_less heap ptr (.forwardPointer forwarded oldValue len) found
    have below : ptr < 2 ^ width / 2 ^ shiftLength conf := Nat.lt_of_lt_of_le ptrBound heapBound
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right below (Nat.two_pow_pos _)) (Nat.div_mul_le_self _ _)
  have read : memory (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr) =
      .word (BitVec.ofNat width forwarded <<< (2 : Nat)) ∧
      domain (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr) = true := by
    have graph : SetSep.fun2Set (memory, fun address => domain address = true)
        (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
          .word (BitVec.ofNat width forwarded <<< (2 : Nat))) := by
      obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split heap ptr _ found
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
  simp only [CopyingGc.gcMove, found, Prod.mk.injEq] at abstractRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl, _⟩ := abstractRun
  simp only [wordAddr, wordGcMove, ite_eq_right low, addr, read.1, read.2,
    shiftedForward_isForward, ↓reduceIte, wordSemTheWord, Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
  refine ⟨xs, ?_, ?_, rfl, rfl, rfl, length.symm, ?_⟩
  · simpa [wordHeap, starEmptyRight] using separated
  · simp only [wordAddr, updateAddr_forward]
  · simp [heapLength]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
