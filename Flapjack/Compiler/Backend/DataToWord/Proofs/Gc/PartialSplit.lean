import Flapjack.Compiler.Backend.GcShared.Slice
import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Forward
import Flapjack.Compiler.Backend.GenGcPartial

/-! Heap splitting facts used by the partial generational collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

/-- Forwarding inside a concatenated heap updates exactly the selected side. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_forward_ptr_APPEND"]
theorem gcForwardPtr_append {α β : Type} (first : List (HeapElement α β)) (offset : Nat)
    (second : List (HeapElement α β)) (address : Nat) (value : α) (ok : Bool) :
    gcForwardPtr offset (first ++ second) address value ok =
      if offset < heapLength first then
        let (heap, status) := gcForwardPtr offset first address value ok
        (heap ++ second, status)
      else
        let (heap, status) := gcForwardPtr (offset - heapLength first) second address value ok
        (first ++ heap, status) := by
  induction first generalizing offset with
  | nil => simp [heapLength]
  | cons head tail ih =>
    simp only [List.cons_append, heapLength, List.map_cons, List.sum_cons]
    by_cases zero : offset = 0
    · subst offset
      have positive : 0 < elLength head := by cases head <;> simp [elLength]
      have under : 0 < elLength head + (tail.map elLength).sum := by omega
      simp [gcForwardPtr, under]
    · by_cases inside : offset < elLength head
      · have under : offset < elLength head + (tail.map elLength).sum := by omega
        simp [gcForwardPtr, zero, inside, under]
      · have enough : elLength head ≤ offset := by omega
        have relation : offset < elLength head + (tail.map elLength).sum ↔
            offset - elLength head < (tail.map elLength).sum := by omega
        by_cases below : offset - elLength head < (tail.map elLength).sum
        · have under : offset < elLength head + (tail.map elLength).sum := relation.mpr below
          simp only [gcForwardPtr, zero, ite_false, inside, under, ite_true, ih, heapLength, below]
          cases gcForwardPtr (offset - elLength head) tail address value ok <;> rfl
        · have under : ¬offset < elLength head + (tail.map elLength).sum := by
            intro h; exact below (relation.mp h)
          simp only [gcForwardPtr, zero, ite_false, inside, under, ih, heapLength, below, Nat.sub_sub]

/-- Splitting at the length of a heap prefix recovers both sides. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "heap_split_APPEND"]
theorem heapSplit_append {α β : Type} (first second : List (HeapElement α β)) :
    heapSplit (heapLength first) (first ++ second) = some (first, second) := by
  induction first with
  | nil => cases second <;> simp [heapLength, heapSplit]
  | cons head tail ih =>
    simp only [List.cons_append, heapLength, List.map_cons, List.sum_cons] at ih ⊢
    have positive : 0 < elLength head := by cases head <;> simp [elLength]
    rw [heapSplit]
    simp only [Nat.ne_of_gt (by omega : 0 < elLength head + (tail.map elLength).sum), ite_false,
      Nat.not_lt.mpr (by omega : elLength head ≤ elLength head + (tail.map elLength).sum),
      Nat.add_sub_cancel_left, ih, Option.map_some]

/-- The source's equivalent sum-of-element-lengths formulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "heap_split_APPEND'"]
theorem heapSplit_append_sum {α β : Type} (first second : List (HeapElement α β)) :
    heapSplit ((first.map elLength).sum) (first ++ second) = some (first, second) :=
  heapSplit_append first second

/-- Dropping a complete heap prefix returns the suffix. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "heap_drop_APPEND"]
theorem heapDrop_append {α β : Type} (first second : List (HeapElement α β)) :
    heapDrop (heapLength first) (first ++ second) = second := by
  simp [heapDrop, heapSplit_append]

/-- Taking a complete heap prefix returns that prefix. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "heap_take_APPEND"]
theorem heapTake_append {α β : Type} (first second : List (HeapElement α β)) :
    heapTake (heapLength first) (first ++ second) = first := by
  simp [heapTake, heapSplit_append]

/-- Dropping zero words leaves the heap unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "heap_drop_0"]
theorem heapDrop_zero {α β : Type} (heap : List (HeapElement α β)) : heapDrop 0 heap = heap := by
  cases heap <;> simp [heapDrop, heapSplit]

/-- Forwarding an element in the middle region preserves the surrounding
heap segments. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_forward_ptr_heap_split"]
theorem gcForwardPtr_heapSplit {α β : Type} (first middle : List (HeapElement α β)) (offset : Nat)
    (last : List (HeapElement α β)) (roots : List (HeapAddress α)) (len : Nat) (payload : β)
    (ok ok1 : Bool) (heap : List (HeapElement α β)) (address : Nat) (value : α)
    (_lookup : heapLookup offset (first ++ middle ++ last) = some (.dataElement roots len payload))
    (run : gcForwardPtr offset (first ++ middle ++ last) address value ok = (heap, ok1))
    (lower : heapLength first ≤ offset) (upper : offset < heapLength (first ++ middle)) :
    heap = first ++ heapTake (heapLength middle) (heapDrop (heapLength first) heap) ++ last := by
  have within : offset - heapLength first < heapLength middle := by
    rw [heapLength_append] at upper
    omega
  rw [List.append_assoc, gcForwardPtr_append] at run
  simp only [Nat.not_lt.mpr lower, ite_false] at run
  rw [gcForwardPtr_append] at run
  simp only [within, ite_true] at run
  cases forwarded : gcForwardPtr (offset - heapLength first) middle address value ok with
  | mk middle1 status =>
    simp only [forwarded, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    have equal := GenGcPartial.gcForwardPtr_heapLength (offset - heapLength first) middle address value ok middle1 status forwarded
    simp only [List.append_assoc, heapDrop_append]
    rw [equal, heapTake_append]

/-- Moving one root in a partial collection leaves the old and reference
regions of the segmented heap unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "partial_gc_move_heap_split"]
theorem partialGcMove_heapSplit {α β : Type} (conf : GenGcPartial.Config β)
    (state state1 : GcState α β) (root root1 : HeapAddress α)
    (first middle last : List (HeapElement α β))
    (run : GenGcPartial.gcMove conf state root = (root1, state1))
    (segment : heapSegment (conf.genStart, conf.refsStart) state.heap = some (first, middle, last))
    (_ordered : conf.genStart ≤ conf.refsStart) :
    state1.heap = first ++ heapTake (heapLength middle) (heapDrop (heapLength first) state1.heap) ++ last := by
  obtain ⟨heapEq, firstLen, nextLen, _⟩ :=
    heapSegment_imp state.heap conf.genStart conf.refsStart first middle last segment
  have original : state.heap = first ++ heapTake (heapLength middle) (heapDrop (heapLength first) state.heap) ++ last := by
    rw [← heapEq]
    simp only [List.append_assoc, heapDrop_append, heapTake_append]
  cases root with
  | data value =>
    simp only [GenGcPartial.gcMove, Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    exact original
  | pointer ptr value =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [GenGcPartial.gcMove, outside, Prod.mk.injEq] at run
      obtain ⟨_, rfl⟩ := run
      exact original
    · have lower : heapLength first ≤ ptr := by omega
      have upper : ptr < heapLength (first ++ middle) := by omega
      cases found : heapLookup ptr state.heap with
      | none =>
        simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run
        obtain ⟨_, rfl⟩ := run
        exact original
      | some element =>
        cases element with
        | unused len =>
          simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run
          obtain ⟨_, rfl⟩ := run
          exact original
        | forwardPointer dest old len =>
          simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run
          obtain ⟨_, rfl⟩ := run
          exact original
        | dataElement roots len payload =>
          cases forward : gcForwardPtr ptr state.heap state.a value
              ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload)) with
          | mk newHeap status =>
            simp only [GenGcPartial.gcMove, outside, ↓reduceIte, found, forward,
              Prod.mk.injEq] at run
            obtain ⟨_, rfl⟩ := run
            exact gcForwardPtr_heapSplit first middle ptr last roots len payload
              ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload))
              status newHeap state.a value (by simpa [heapEq] using found)
              (by simpa [heapEq] using forward) lower upper

/-- Moving a list of roots preserves the old and reference heap regions. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "partial_gc_move_list_heap_split"]
theorem partialGcMoveList_heapSplit {α β : Type} (roots : List (HeapAddress α))
    (conf : GenGcPartial.Config β) (state : GcState α β) (roots1 : List (HeapAddress α)) (state1 : GcState α β)
    (first middle last : List (HeapElement α β))
    (run : GenGcPartial.gcMoveList conf state roots = (roots1, state1))
    (segment : heapSegment (conf.genStart, conf.refsStart) state.heap = some (first, middle, last))
    (ordered : conf.genStart ≤ conf.refsStart) :
    state1.heap = first ++ heapTake (heapLength middle) (heapDrop (heapLength first) state1.heap) ++ last := by
  induction roots generalizing state state1 roots1 middle with
  | nil =>
    simp only [GenGcPartial.gcMoveList, Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    obtain ⟨heapEq, _, _, _⟩ := heapSegment_imp state.heap _ _ first middle last segment
    rw [← heapEq]
    simp only [List.append_assoc, heapDrop_append, heapTake_append]
  | cons root roots ih =>
    simp only [GenGcPartial.gcMoveList] at run
    generalize headRun : GenGcPartial.gcMove conf state root = result at run
    obtain ⟨rootMid, stateMid⟩ := result
    generalize tailRun : GenGcPartial.gcMoveList conf stateMid roots = result at run
    obtain ⟨rootsMid, stateEnd⟩ := result
    simp only [Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    obtain ⟨heapEq, firstLen, nextLen, _⟩ := heapSegment_imp state.heap _ _ first middle last segment
    have midEq := partialGcMove_heapSplit conf state stateMid root rootMid first middle last headRun segment ordered
    have heapLen := GenGcPartial.gcMove_heapLength conf state stateMid root rootMid headRun
    let changed := heapTake (heapLength middle) (heapDrop (heapLength first) stateMid.heap)
    have midEq' : stateMid.heap = first ++ changed ++ last := midEq
    have changedLen : heapLength changed = heapLength middle := by
      rw [← heapEq, midEq'] at heapLen
      simp only [heapLength_append] at heapLen
      omega
    have midSegment : heapSegment (conf.genStart, conf.refsStart) stateMid.heap = some (first, changed, last) := by
      rw [midEq', ← firstLen, ← nextLen]
      simp only [heapSegment, List.append_assoc, heapSplit_append, heapLength_append,
        Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte, Nat.add_sub_cancel_left]
      rw [← changedLen, heapSplit_append]
      rfl
    have finalEq := ih stateMid rootsMid stateEnd changed tailRun midSegment
    simpa only [changedLen] using finalEq

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
