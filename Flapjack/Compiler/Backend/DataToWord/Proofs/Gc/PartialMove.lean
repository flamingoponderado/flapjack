module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialSplit
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Generational
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PointerAddress
public import Flapjack.Compiler.Backend.GenGc.Proofs.HeapLookup
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveForward
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveBlock

@[expose] public section

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
    ite_eq_right (Nat.not_lt.mpr lower), GenGc.heapLookup_append] at found
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
  simp only [wordAddr, wordGenGcPartialMove, low', ite_false, outsideWord, ite_true, Prod.mk.injEq] at wordRun
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
  simp only [wordAddr, wordGenGcPartialMove, low', ite_false, inWord] at wordRun
  simp only [addr', read.1, read.2,
    shiftedForward_isForward, ite_true, wordSemTheWord, Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
  refine ⟨xs, current, ?_, ?_, rfl, segment, rfl, rfl, length.symm, ?_, ?_⟩
  · simpa [h2Empty, wordHeap, partialStarEmptyRight] using separated
  · simp only [wordAddr, updateAddr_forward]
  · simp [h2Empty, r4Empty, heapLength]
  · simp [h2Empty, heapLength]

/-- The in-generation data-object case of the partial move theorem. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_partial_move_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMove_copy {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (ptr len : Nat) (value : WordLocW width)
    (addresses : List (HeapAddress (WordLocW width))) (tag : HeapTag) (payload : List (WordLocW width)) (root1 : HeapAddress (WordLocW width))
    (old current refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa i1 pa1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (w : WordLocW width) (c1 : Bool)
    (abstractRun : GenGcPartial.gcMove genConf state (.pointer ptr value) = (root1, state1))
    (h2Empty : state.h2 = []) (r4Empty : state.r4 = []) (stateOk : state1.ok = true)
    (_limitEq : genConf.limit = heapLength state.heap) (good : goodDimindex width)
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (_ordered : genConf.genStart ≤ genConf.refsStart) (refBound : genConf.refsStart ≤ heapLength state.heap)
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
    (found : heapLookup ptr state.heap = some (.dataElement addresses len (tag, payload))) :
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
  classical
  have outside : ¬(ptr < genConf.genStart ∨ genConf.refsStart ≤ ptr) := by omega
  have currentFound := partialHeapLookup_middle state.heap old current refs genConf.genStart genConf.refsStart ptr
    (.dataElement addresses len (tag, payload)) segment inside.1 inside.2 found
  obtain ⟨heapEq, oldLen, endLen, _⟩ := heapSegment_imp state.heap _ _ old current refs segment
  obtain ⟨before, after, currentEq, ptrEq⟩ := heapLookup_split current (ptr - genConf.genStart) _ currentFound
  have ptrFull : ptr = heapLength (old ++ before) := by
    rw [heapLength_append, oldLen, ← ptrEq]
    omega
  have wholeEq : state.heap = (old ++ before) ++ .dataElement addresses len (tag, payload) :: (after ++ refs) := by
    rw [← heapEq, currentEq]
    simp [List.append_assoc]
  have forwardWhole (ok : Bool) : gcForwardPtr ptr state.heap state.a value ok =
      ((old ++ before) ++ .forwardPointer state.a value len :: (after ++ refs), ok) := by
    rw [wholeEq, ptrFull]
    exact gcForwardPtr_thm (old ++ before) (after ++ refs) addresses len (tag, payload) state.a value ok
  simp only [GenGcPartial.gcMove, outside, ↓reduceIte, found, forwardWhole, Prod.mk.injEq] at abstractRun
  obtain ⟨rfl, rfl⟩ := abstractRun
  simp only [Bool.and_eq_true, decide_eq_true_eq] at stateOk
  have space : len + 1 ≤ state.n := stateOk.1.2
  have relativeAddr :
      (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) +
        wordSemBytesInWord * BitVec.ofNat width (ptr - genConf.genStart) =
      curr + wordSemBytesInWord * BitVec.ofNat width ptr := by
    rw [BitVec.add_assoc, ← BitVec.mul_add, ← BitVec.ofNat_add, oldLen,
      Nat.add_sub_of_le inside.1]
  have currentBound : heapLength current ≤ 2 ^ width / 2 ^ shiftLength conf := by
    have le : heapLength current ≤ heapLength state.heap := by
      rw [← heapEq, heapLength_append, heapLength_append]
      omega
    exact le.trans heapBound
  have ptrBound : ptr * 2 ^ shiftLength conf < 2 ^ width := by
    have below : ptr < 2 ^ width / 2 ^ shiftLength conf := Nat.lt_of_lt_of_le stateOk.1.1.2 heapBound
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right below (Nat.two_pow_pos _)) (Nat.div_mul_le_self _ _)
  have relBound : (ptr - genConf.genStart) * 2 ^ shiftLength conf < 2 ^ width := by
    have below : ptr - genConf.genStart < 2 ^ width / 2 ^ shiftLength conf :=
      Nat.lt_of_lt_of_le (heapLookup_less current _ _ currentFound) currentBound
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right below (Nat.two_pow_pos _)) (Nat.div_mul_le_self _ _)
  have offsetEq : ptrToAddr conf curr (getAddr conf ptr value) - curr =
      wordSemBytesInWord * BitVec.ofNat width ptr := by
    rw [ptrToAddr_getAddr conf curr ptr value ptrBound]
    simp only [BitVec.add_comm curr, BitVec.add_sub_cancel, BitVec.mul_comm]
  have less := partialByteOffsets_order ptr genConf.genStart (heapLength state.heap) good (by omega) (by omega) byteBound
  have more := partialByteOffsets_order genConf.refsStart ptr (heapLength state.heap) good (by omega) (by omega) byteBound
  have inWord : ¬(ptrToAddr conf curr (getAddr conf ptr value) - curr < wordSemBytesInWord * BitVec.ofNat width genConf.genStart ∨
      wordSemBytesInWord * BitVec.ofNat width genConf.refsStart ≤ ptrToAddr conf curr (getAddr conf ptr value) - curr) := by
    rw [offsetEq, less.1, more.2]
    exact outside
  obtain ⟨header, words, encoded, wordLen, wordBound, decoded, cell⟩ :=
    wordHeap_dataCell conf before after addresses len tag payload
      (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) pa xs memory domain frame
      (by simpa only [← currentEq] using separated)
  let src := curr + wordSemBytesInWord * BitVec.ofNat width ptr
  have read : memory src = .word header ∧ domain src = true := by
    have graph : SetSep.fun2Set (memory, fun address => domain address = true) (src, .word header) := by
      rcases cell with ⟨sourceAndFrame, free, outSplit, sourceAndFrameAssert, _⟩
      rcases sourceAndFrameAssert with ⟨rest, source, sourceSplit, _, sourceAssert⟩
      have entry := StackRemove.StackHeap.wordListNth
        ((curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) +
          StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before))
        (.word header :: words) source 0 (by simp) sourceAssert
      rw [← outSplit.1, ← sourceSplit.1]
      apply Or.inl
      apply Or.inr
      have entry' : source
          ((curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) +
            wordSemBytesInWord * BitVec.ofNat width (ptr - genConf.genStart), .word header) := by
        simpa [← ptrEq, wordSemBytesInWord, StackRemove.bytesInWord] using entry
      rw [relativeAddr] at entry'
      exact entry'
    exact (SetSep.fun2SetThm memory _ _ _).mp graph
  have low : getAddr conf ptr value &&& (1 : BitVec width) ≠ 0 := by
    simpa only [BitVec.and_comm] using getAddr_and_one_ne_zero conf ptr value
  have address : ptrToAddr conf curr (getAddr conf ptr value) = src := by
    simpa only [src, BitVec.mul_comm] using ptrToAddr_getAddr conf curr ptr value ptrBound
  have notForward : wordSemIsFwdPtr (.word header) = false :=
    wordPayload_not_fwdPtr conf addresses len tag payload header words true encoded
  simp only [wordAddr, wordGenGcPartialMove, low, ite_false, inWord] at wordRun
  simp only [address, read.1, read.2, notForward, Bool.false_eq_true, ↓reduceIte,
    wordSemTheWord, wordSemIsWordLoc, Bool.true_and, decoded] at wordRun
  generalize copyRun : memcpy (BitVec.ofNat width words.length + 1) src pa memory domain = copyResult at wordRun
  rcases copyResult with ⟨copyEnd, copyMemory, copyOk⟩
  simp only [Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
  have relLow : getAddr conf (ptr - genConf.genStart) value &&& (1 : BitVec width) ≠ 0 := by
    simpa only [BitVec.and_comm] using getAddr_and_one_ne_zero conf (ptr - genConf.genStart) value
  have relAddr : ptrToAddr conf (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old))
      (getAddr conf (ptr - genConf.genStart) value) = src := by
    rw [ptrToAddr_getAddr conf _ _ value relBound]
    simpa only [src, wordSemBytesInWord, BitVec.mul_comm] using relativeAddr
  have copyWordRun : wordGcMove conf
      (wordAddr conf (.pointer (ptr - genConf.genStart) value), BitVec.ofNat width state.a, pa,
        curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old), memory, domain) =
      (.word (updateAddr conf (BitVec.ofNat width state.a) (getAddr conf (ptr - genConf.genStart) value)),
        BitVec.ofNat width state.a + BitVec.ofNat width words.length + 1,
        copyEnd, gcUpdate src (.word (BitVec.ofNat width state.a <<< (2 : Nat))) copyMemory, copyOk) := by
    simp only [wordAddr, wordGcMove, ite_eq_right relLow, relAddr, read.1, read.2, notForward,
      Bool.false_eq_true, ↓reduceIte, wordSemTheWord, wordSemIsWordLoc, Bool.true_and, decoded, copyRun]
  have forwardCurrent (ok : Bool) : gcForwardPtr (ptr - genConf.genStart) current state.a value ok =
      (before ++ .forwardPointer state.a value len :: after, ok) := by
    rw [currentEq, ptrEq]
    exact gcForwardPtr_thm before after addresses len (tag, payload) state.a value ok
  have copyAbstract : CopyingGc.gcMove (.pointer (ptr - genConf.genStart) value, [], state.a, state.n, current, true,
      state.a + state.n) =
      (.pointer state.a value, [.dataElement addresses len (tag, payload)], state.a + len + 1,
        state.n - (len + 1), before ++ .forwardPointer state.a value len :: after, true) := by
    simp [CopyingGc.gcMove, currentFound, forwardCurrent, space, Nat.add_assoc]
  obtain ⟨remaining, copiedSep, rootEq, heapLen, ok, indexEq, remainingLen, paEq⟩ :=
    wordGcMove_dataElement conf (ptr - genConf.genStart) len value addresses tag payload state.a state.n
      (state.a + state.n) (state.a + len + 1) (state.n - (len + 1)) current
      (before ++ .forwardPointer state.a value len :: after) [.dataElement addresses len (tag, payload)]
      (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) pa copyEnd
      (BitVec.ofNat width state.a + BitVec.ofNat width words.length + 1) xs memory
      (gcUpdate src (.word (BitVec.ofNat width state.a <<< (2 : Nat))) copyMemory) domain frame
      (.pointer state.a value)
      (.word (updateAddr conf (BitVec.ofNat width state.a) (getAddr conf (ptr - genConf.genStart) value)))
      copyOk currentFound copyAbstract currentBound separated copyWordRun length
  have newSegment : heapSegment (genConf.genStart, genConf.refsStart)
      ((old ++ before) ++ .forwardPointer state.a value len :: (after ++ refs)) =
      some (old, before ++ .forwardPointer state.a value len :: after, refs) := by
    rw [← oldLen, ← endLen]
    simp only [List.append_assoc, heapSegment, heapSplit_append, heapLength_append,
      Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte, Nat.add_sub_cancel_left]
    rw [← heapLen]
    have split : heapSplit (heapLength (before ++ .forwardPointer state.a value len :: after))
        (before ++ .forwardPointer state.a value len :: (after ++ refs)) =
        some (before ++ .forwardPointer state.a value len :: after, refs) := by
      simpa only [List.append_assoc, List.cons_append] using
        heapSplit_append (before ++ .forwardPointer state.a value len :: after) refs
    rw [split]
    rfl
  refine ⟨remaining, before ++ .forwardPointer state.a value len :: after, ?_, ?_, ?_, newSegment,
    ok, indexEq, remainingLen, ?_, ?_⟩
  · simpa [h2Empty] using copiedSep
  · simp only [wordAddr, updateAddr_data]
  · rw [wholeEq]
    simp [heapLength, elLength, List.map_append, List.sum_append, Nat.add_assoc]
  · simp only [h2Empty, r4Empty, List.nil_append, heapLength, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, elLength]
    omega
  · simpa [h2Empty] using paEq

/-- Original partial generational collector root-move simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_partial_move_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMove_thm {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (root root1 : HeapAddress (WordLocW width))
    (old current refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa i1 pa1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (w : WordLocW width) (c1 : Bool)
    (abstractRun : GenGcPartial.gcMove genConf state root = (root1, state1))
    (h2Empty : state.h2 = []) (r4Empty : state.r4 = []) (stateOk : state1.ok = true)
    (limitEq : genConf.limit = heapLength state.heap) (good : goodDimindex width)
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (ordered : genConf.genStart ≤ genConf.refsStart) (refBound : genConf.refsStart ≤ heapLength state.heap)
    (segment : heapSegment (genConf.genStart, genConf.refsStart) state.heap = some (old, current, refs))
    (byteBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (separated : SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (Misc.wordList pa xs)) frame (SetSep.fun2Set (memory, fun address => domain address = true)))
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (wordRun : wordGenGcPartialMove conf
      (wordAddr conf root, BitVec.ofNat width state.a, pa, curr, memory, domain,
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
  cases root with
  | data value =>
    exact wordGenGcPartialMove_data conf genConf state state1 value root1 old current refs curr pa i1 pa1 xs
      memory memory1 domain frame w c1 abstractRun h2Empty r4Empty stateOk limitEq good heapBound ordered refBound
      segment byteBound separated refClass wordRun length
  | pointer ptr value =>
    by_cases outside : ptr < genConf.genStart ∨ genConf.refsStart ≤ ptr
    · exact wordGenGcPartialMove_outside conf genConf state state1 ptr value root1 old current refs curr pa i1 pa1 xs
        memory memory1 domain frame w c1 abstractRun h2Empty r4Empty stateOk limitEq good heapBound ordered refBound
        segment byteBound separated refClass wordRun length outside
    · have inside : genConf.genStart ≤ ptr ∧ ptr < genConf.refsStart := by omega
      cases found : heapLookup ptr state.heap with
      | none =>
        simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at abstractRun
        obtain ⟨_, rfl⟩ := abstractRun
        simp at stateOk
      | some element =>
        cases element with
        | unused len =>
          simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at abstractRun
          obtain ⟨_, rfl⟩ := abstractRun
          simp at stateOk
        | forwardPointer target oldValue len =>
          exact wordGenGcPartialMove_forward conf genConf state state1 ptr target len value oldValue root1 old current refs
            curr pa i1 pa1 xs memory memory1 domain frame w c1 abstractRun h2Empty r4Empty stateOk limitEq good heapBound
            ordered refBound segment byteBound separated refClass wordRun length inside found
        | dataElement addresses len payload =>
          obtain ⟨tag, payload⟩ := payload
          exact wordGenGcPartialMove_copy conf genConf state state1 ptr len value addresses tag payload root1 old current refs
            curr pa i1 pa1 xs memory memory1 domain frame w c1 abstractRun h2Empty r4Empty stateOk limitEq good heapBound
            ordered refBound segment byteBound separated refClass wordRun length inside found

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
