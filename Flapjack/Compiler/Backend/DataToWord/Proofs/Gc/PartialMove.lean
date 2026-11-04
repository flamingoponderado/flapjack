import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialSplit
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Generational
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PointerAddress
import Flapjack.Compiler.Backend.GenGc.Proofs.HeapLookup
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveForward

/-! Partial generational collector root-move simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem partialClearLowBit {width : Nat} (value : BitVec width) :
    (value &&& ~~~(1 : BitVec width)) &&& 1 = 0 := by
  rw [BitVec.and_assoc]
  simp

private theorem partialStarEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]

private theorem partialShiftedForward_isForward {width : Nat} [NeZero width] (value : BitVec width) :
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

/-- Byte-scaled offsets preserve ordering within a heap whose byte length fits
in a machine word. This is arithmetic used by the partial collector proof. -/
theorem partialByteOffsets_order {width : Nat} [NeZero width] (a b limit : Nat)
    (good : goodDimindex width) (aBound : a ≤ limit) (bBound : b ≤ limit)
    (byteBound : limit * (width / 8) < 2 ^ width) :
    ((wordSemBytesInWord * BitVec.ofNat width a : BitVec width) <
       wordSemBytesInWord * BitVec.ofNat width b ↔ a < b) ∧
    ((wordSemBytesInWord * BitVec.ofNat width a : BitVec width) ≤
       wordSemBytesInWord * BitVec.ofNat width b ↔ a ≤ b) := by
  have positive : 0 < width / 8 := by rcases good with rfl | rfl <;> decide
  have aBytes : a * (width / 8) < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ aBound) byteBound
  have bBytes : b * (width / 8) < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ bBound) byteBound
  have aValue : ((wordSemBytesInWord : BitVec width) * BitVec.ofNat width a).toNat = a * (width / 8) := by
    simp only [wordSemBytesInWord, BitVec.mul_comm, ← BitVec.ofNat_mul, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt aBytes]
  have bValue : ((wordSemBytesInWord : BitVec width) * BitVec.ofNat width b).toNat = b * (width / 8) := by
    simp only [wordSemBytesInWord, BitVec.mul_comm, ← BitVec.ofNat_mul, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt bBytes]
  simp only [BitVec.lt_def, BitVec.le_def, aValue, bValue]
  refine ⟨Nat.mul_lt_mul_right positive, ?_⟩
  constructor
  · intro h; exact Nat.le_of_mul_le_mul_right h positive
  · exact Nat.mul_le_mul_right _

/-- A pointer in the collected generation selects the corresponding element
of the middle heap segment. -/
theorem partialHeapLookup_middle {α β : Type} (heap old current refs : List (HeapElement α β))
    (start finish ptr : Nat) (element : HeapElement α β)
    (segment : heapSegment (start, finish) heap = some (old, current, refs))
    (lower : start ≤ ptr) (upper : ptr < finish)
    (found : heapLookup ptr heap = some element) :
    heapLookup (ptr - start) current = some element := by
  obtain ⟨heapEq, oldLen, endLen, _⟩ := heapSegment_imp heap start finish old current refs segment
  rw [← heapEq, List.append_assoc, GenGc.heapLookup_append, oldLen,
    if_neg (Nat.not_lt.mpr lower), GenGc.heapLookup_append] at found
  have inside : ptr - start < heapLength current := by
    rw [heapLength_append, oldLen] at endLen
    omega
  simpa [inside] using found

/-- The immediate-data case of the partial generational root-move theorem. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_partial_move_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMove_data {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (value : WordLocW width) (root1 : HeapAddress (WordLocW width))
    (old current refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa i1 pa1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (w : WordLocW width) (c1 : Bool)
    (abstractRun : GenGcPartial.gcMove genConf state (.data value) = (root1, state1))
    (h2Empty : state.h2 = []) (r4Empty : state.r4 = []) (_stateOk : state1.ok = true)
    (_limitEq : genConf.limit = heapLength state.heap) (_good : goodDimindex width)
    (_heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (_ordered : genConf.genStart ≤ genConf.refsStart) (_refBound : genConf.refsStart ≤ heapLength state.heap)
    (segment : heapSegment (genConf.genStart, genConf.refsStart) state.heap = some (old, current, refs))
    (_byteBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (separated : SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (Misc.wordList pa xs)) frame (SetSep.fun2Set (memory, fun address => domain address = true)))
    (_refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (wordRun : wordGenGcPartialMove conf
      (wordAddr conf (.data value), BitVec.ofNat width state.a, pa, curr, memory, domain,
       wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
       wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = (w, i1, pa1, memory1, c1))
    (length : xs.length = state.n) :
    ∃ xs1 current1,
      SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current1 conf)
        (wordHeap pa state1.h2 conf)) (Misc.wordList pa1 xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      w = wordAddr conf root1 ∧ heapLength state1.heap = heapLength state.heap ∧
      heapSegment (genConf.genStart, genConf.refsStart) state1.heap = some (old, current1, refs) ∧
      c1 = true ∧ i1 = BitVec.ofNat width state1.a ∧ state1.n = xs1.length ∧
      state.n = heapLength state1.h2 + state1.n + heapLength state1.r4 ∧
      pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h2) := by
  simp only [GenGcPartial.gcMove, Prod.mk.injEq] at abstractRun
  obtain ⟨rfl, rfl⟩ := abstractRun
  cases value with
  | loc l1 l2 =>
    simp only [wordAddr, wordGenGcPartialMove, decide_true, Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    refine ⟨xs, current, ?_, rfl, rfl, segment, rfl, rfl, length.symm, ?_, ?_⟩
    · simpa [h2Empty, wordHeap, partialStarEmptyRight] using separated
    · simp [h2Empty, r4Empty, heapLength]
    · simp [h2Empty, heapLength]
  | word bits =>
    simp only [wordAddr, wordGenGcPartialMove, partialClearLowBit, ↓reduceIte, Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    refine ⟨xs, current, ?_, rfl, rfl, segment, rfl, rfl, length.symm, ?_, ?_⟩
    · simpa [h2Empty, wordHeap, partialStarEmptyRight] using separated
    · simp [h2Empty, r4Empty, heapLength]
    · simp [h2Empty, heapLength]

/-- The outside-generation pointer case of the partial move theorem. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_partial_move_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMove_outside {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (ptr : Nat) (value : WordLocW width) (root1 : HeapAddress (WordLocW width))
    (old current refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa i1 pa1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (w : WordLocW width) (c1 : Bool)
    (abstractRun : GenGcPartial.gcMove genConf state (.pointer ptr value) = (root1, state1))
    (h2Empty : state.h2 = []) (r4Empty : state.r4 = []) (stateOk : state1.ok = true)
    (_limitEq : genConf.limit = heapLength state.heap) (good : goodDimindex width)
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (ordered : genConf.genStart ≤ genConf.refsStart) (refBound : genConf.refsStart ≤ heapLength state.heap)
    (segment : heapSegment (genConf.genStart, genConf.refsStart) state.heap = some (old, current, refs))
    (byteBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (separated : SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (Misc.wordList pa xs)) frame (SetSep.fun2Set (memory, fun address => domain address = true)))
    (_refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (wordRun : wordGenGcPartialMove conf
      (wordAddr conf (.pointer ptr value), BitVec.ofNat width state.a, pa, curr, memory, domain,
       wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
       wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = (w, i1, pa1, memory1, c1))
    (length : xs.length = state.n)
    (outside : ptr < genConf.genStart ∨ genConf.refsStart ≤ ptr) :
    ∃ xs1 current1,
      SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current1 conf)
        (wordHeap pa state1.h2 conf)) (Misc.wordList pa1 xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      w = wordAddr conf root1 ∧ heapLength state1.heap = heapLength state.heap ∧
      heapSegment (genConf.genStart, genConf.refsStart) state1.heap = some (old, current1, refs) ∧
      c1 = true ∧ i1 = BitVec.ofNat width state1.a ∧ state1.n = xs1.length ∧
      state.n = heapLength state1.h2 + state1.n + heapLength state1.r4 ∧
      pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h2) := by
  simp only [GenGcPartial.gcMove, outside, ↓reduceIte, Prod.mk.injEq] at abstractRun
  obtain ⟨rfl, rfl⟩ := abstractRun
  simp only [Bool.and_eq_true, decide_eq_true_eq] at stateOk
  have ptrInHeap : ptr < heapLength state.heap := stateOk.2
  have ptrBound : ptr * 2 ^ shiftLength conf < 2 ^ width := by
    have below : ptr < 2 ^ width / 2 ^ shiftLength conf := Nat.lt_of_lt_of_le ptrInHeap heapBound
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right below (Nat.two_pow_pos _)) (Nat.div_mul_le_self _ _)
  have low := getAddr_and_one_ne_zero conf ptr value
  have address := ptrToAddr_getAddr conf curr ptr value ptrBound
  have less := partialByteOffsets_order ptr genConf.genStart (heapLength state.heap) good (by omega) (by omega) byteBound
  have more := partialByteOffsets_order genConf.refsStart ptr (heapLength state.heap) good (by omega) (by omega) byteBound
  have offsetEq : ptrToAddr conf curr (getAddr conf ptr value) - curr =
      wordSemBytesInWord * BitVec.ofNat width ptr := by
    rw [address]
    simp only [BitVec.add_comm curr, BitVec.add_sub_cancel, BitVec.mul_comm]
  have outsideWord :
      ptrToAddr conf curr (getAddr conf ptr value) - curr < wordSemBytesInWord * BitVec.ofNat width genConf.genStart ∨
      wordSemBytesInWord * BitVec.ofNat width genConf.refsStart ≤ ptrToAddr conf curr (getAddr conf ptr value) - curr := by
    rw [offsetEq]
    exact outside.elim (fun h => Or.inl (less.1.mpr h)) (fun h => Or.inr (more.2.mpr h))
  have low' : getAddr conf ptr value &&& (1 : BitVec width) ≠ 0 := by
    simpa [BitVec.and_comm] using low
  simp only [wordAddr, wordGenGcPartialMove, low', if_false, outsideWord, if_true, Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
  refine ⟨xs, current, ?_, rfl, rfl, segment, rfl, rfl, length.symm, ?_, ?_⟩
  · simpa [h2Empty, wordHeap, partialStarEmptyRight] using separated
  · simp [h2Empty, r4Empty, heapLength]
  · simp [h2Empty, heapLength]

/-- The forwarding-pointer case of the partial move theorem. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_partial_move_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMove_forward {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (ptr forwarded len : Nat) (value oldValue : WordLocW width) (root1 : HeapAddress (WordLocW width))
    (old current refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa i1 pa1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (w : WordLocW width) (c1 : Bool)
    (abstractRun : GenGcPartial.gcMove genConf state (.pointer ptr value) = (root1, state1))
    (h2Empty : state.h2 = []) (r4Empty : state.r4 = []) (stateOk : state1.ok = true)
    (_limitEq : genConf.limit = heapLength state.heap) (good : goodDimindex width)
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (ordered : genConf.genStart ≤ genConf.refsStart) (refBound : genConf.refsStart ≤ heapLength state.heap)
    (segment : heapSegment (genConf.genStart, genConf.refsStart) state.heap = some (old, current, refs))
    (byteBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (separated : SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (Misc.wordList pa xs)) frame (SetSep.fun2Set (memory, fun address => domain address = true)))
    (_refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (wordRun : wordGenGcPartialMove conf
      (wordAddr conf (.pointer ptr value), BitVec.ofNat width state.a, pa, curr, memory, domain,
       wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
       wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = (w, i1, pa1, memory1, c1))
    (length : xs.length = state.n)
    (inside : genConf.genStart ≤ ptr ∧ ptr < genConf.refsStart)
    (found : heapLookup ptr state.heap = some (.forwardPointer forwarded oldValue len)) :
    ∃ xs1 current1,
      SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current1 conf)
        (wordHeap pa state1.h2 conf)) (Misc.wordList pa1 xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      w = wordAddr conf root1 ∧ heapLength state1.heap = heapLength state.heap ∧
      heapSegment (genConf.genStart, genConf.refsStart) state1.heap = some (old, current1, refs) ∧
      c1 = true ∧ i1 = BitVec.ofNat width state1.a ∧ state1.n = xs1.length ∧
      state.n = heapLength state1.h2 + state1.n + heapLength state1.r4 ∧
      pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h2) := by
  have outside : ¬(ptr < genConf.genStart ∨ genConf.refsStart ≤ ptr) := by omega
  have ptrInHeap : ptr < heapLength state.heap := by omega
  have ptrBound : ptr * 2 ^ shiftLength conf < 2 ^ width := by
    have below : ptr < 2 ^ width / 2 ^ shiftLength conf := Nat.lt_of_lt_of_le ptrInHeap heapBound
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right below (Nat.two_pow_pos _)) (Nat.div_mul_le_self _ _)
  have low := getAddr_and_one_ne_zero conf ptr value
  have address := ptrToAddr_getAddr conf curr ptr value ptrBound
  have less := partialByteOffsets_order ptr genConf.genStart (heapLength state.heap) good (by omega) (by omega) byteBound
  have more := partialByteOffsets_order genConf.refsStart ptr (heapLength state.heap) good (by omega) (by omega) byteBound
  have offsetEq : ptrToAddr conf curr (getAddr conf ptr value) - curr =
      wordSemBytesInWord * BitVec.ofNat width ptr := by
    rw [address]
    simp only [BitVec.add_comm curr, BitVec.add_sub_cancel, BitVec.mul_comm]
  have inWord : ¬(ptrToAddr conf curr (getAddr conf ptr value) - curr < wordSemBytesInWord * BitVec.ofNat width genConf.genStart ∨
      wordSemBytesInWord * BitVec.ofNat width genConf.refsStart ≤ ptrToAddr conf curr (getAddr conf ptr value) - curr) := by
    rw [offsetEq, less.1, more.2]
    exact outside
  have currentFound := partialHeapLookup_middle state.heap old current refs genConf.genStart genConf.refsStart ptr
    (.forwardPointer forwarded oldValue len) segment inside.1 inside.2 found
  obtain ⟨_, oldLen, _, _⟩ := heapSegment_imp state.heap _ _ old current refs segment
  have relativeAddr :
      (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) +
        wordSemBytesInWord * BitVec.ofNat width (ptr - genConf.genStart) =
      curr + wordSemBytesInWord * BitVec.ofNat width ptr := by
    rw [BitVec.add_assoc, ← BitVec.mul_add, ← BitVec.ofNat_add, oldLen,
      Nat.add_sub_of_le inside.1]
  have read : memory (curr + wordSemBytesInWord * BitVec.ofNat width ptr) =
      .word (BitVec.ofNat width forwarded <<< (2 : Nat)) ∧
      domain (curr + wordSemBytesInWord * BitVec.ofNat width ptr) = true := by
    have graph : SetSep.fun2Set (memory, fun address => domain address = true)
        (curr + wordSemBytesInWord * BitVec.ofNat width ptr,
          .word (BitVec.ofNat width forwarded <<< (2 : Nat))) := by
      obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split current (ptr - genConf.genStart) _ currentFound
      rcases separated with ⟨heapAndList, rest, outSplit, heapAndListAssert, _⟩
      rcases heapAndListAssert with ⟨heapPart, listPart, heapSplit, heapAssert, _⟩
      rw [heapEq, wordHeapAppend] at heapAssert
      rcases heapAssert with ⟨pre, post, preSplit, _, postAssert⟩
      change SetSep.star (wordEl _ (.forwardPointer forwarded oldValue len) conf)
        (wordHeap _ after conf) post at postAssert
      rcases postAssert with ⟨cell, suffix, postSplit, cellAssert, _⟩
      simp only [wordEl] at cellAssert
      rcases cellAssert with ⟨singleton, restCell, cellSplit, singletonEq, _⟩
      rw [← relativeAddr, ptrEq, ← outSplit.1, ← heapSplit.1, ← preSplit.1, ← postSplit.1, ← cellSplit.1]
      exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (by
        rw [singletonEq]
        simp only [wordSemBytesInWord, StackRemove.bytesInWord])))))
    exact (SetSep.fun2SetThm memory _ _ _).mp graph
  simp only [GenGcPartial.gcMove, outside, ↓reduceIte, found, Prod.mk.injEq] at abstractRun
  obtain ⟨rfl, rfl⟩ := abstractRun
  have low' : getAddr conf ptr value &&& (1 : BitVec width) ≠ 0 := by
    simpa [BitVec.and_comm] using low
  have addr' : ptrToAddr conf curr (getAddr conf ptr value) =
      curr + wordSemBytesInWord * BitVec.ofNat width ptr := by
    simpa only [BitVec.mul_comm] using address
  simp only [wordAddr, wordGenGcPartialMove, low', if_false, inWord] at wordRun
  simp only [addr', read.1, read.2,
    partialShiftedForward_isForward, if_true, wordSemTheWord, Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
  refine ⟨xs, current, ?_, ?_, rfl, segment, rfl, rfl, length.symm, ?_, ?_⟩
  · simpa [h2Empty, wordHeap, partialStarEmptyRight] using separated
  · simp only [wordAddr, updateAddr_forward]
  · simp [h2Empty, r4Empty, heapLength]
  · simp [h2Empty, heapLength]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
