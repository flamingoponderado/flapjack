module

public import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Simulation

@[expose] public section

/-!
# Auxiliary facts for partial generational collection

Small lemmas about heap sizes, heap splitting and the translation to the major
collector's address space, together with the source-state invariants
(`has_bad_ref`, `balanced_state`, `simple_rel`) used by the quality argument.
-/

namespace Flapjack.Compiler.Backend.GenGcPartial

/-- A data element with a reference payload in the copied heaps, or a data
element with a reference payload in the current generation, is a bad
reference. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "has_bad_ref_def"]
noncomputable def hasBadRef {α β : Type} (conf : Config α) (state : GcState β α) : Prop :=
  (∃ xs len data, .dataElement xs len data ∈ state.h1 ++ state.h2 ∧ conf.isRef data = true) ∨
    ∃ xs len data ptr, conf.genStart ≤ ptr ∧ ptr < conf.refsStart ∧
      heapLookup ptr state.heap = some (.dataElement xs len data) ∧ conf.isRef data = true

open Classical in
/-- The collector's state is balanced: the forwarding pointers in the heap
account for the copied heaps, and the remaining data fits in the source
segments. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "balanced_state_def"]
noncomputable def balancedState {α β : Type} (conf : Config α) (state : GcState β α) : Prop :=
  heapLength (state.heap.filter isForwardPointer) =
      heapLength state.h1 + heapLength state.h2 ∧
    (match heapSegment (conf.genStart, conf.refsStart) state.heap with
    | none => False
    | some (old, _current, refs) =>
      heapLength (state.r1.filter (fun e => decide (isDataElement e))) +
          heapLength (state.r2.filter (fun e => decide (isDataElement e))) +
          heapLength (state.old.filter (fun e => decide (isDataElement e))) ≤
        heapLength (old.filter (fun e => decide (isDataElement e))) +
          heapLength (refs.filter (fun e => decide (isDataElement e))))

open Classical in
/-- Observable quantities preserved by one step of the partial collection. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "simple_rel_def"]
noncomputable def simpleRel {α β : Type} (conf : Config α) (s1 s2 : GcState β α) : Prop :=
  s2.old = s1.old ∧
  heapLength (s2.h1 ++ s2.h2 ++ heapExpand s2.n) =
      heapLength (s1.h1 ++ s1.h2 ++ heapExpand s1.n) ∧
  (s1.a = conf.genStart + heapLength s1.h1 + heapLength s1.h2 →
    s2.a = conf.genStart + heapLength s2.h1 + heapLength s2.h2) ∧
  (List.Forall isDataElement s1.h1 → List.Forall isDataElement s2.h1) ∧
  heapLength (s1.heap.filter (fun e => decide (isDataElement e)) ++ s1.h1 ++ s1.h2) =
      heapLength (s2.heap.filter (fun e => decide (isDataElement e)) ++ s2.h1 ++ s2.h2) ∧
  heapLength (s1.heap.filter isForwardPointer) +
        heapLength (s1.heap.filter (fun e => decide (isDataElement e))) =
      heapLength (s2.heap.filter isForwardPointer) +
        heapLength (s2.heap.filter (fun e => decide (isDataElement e))) ∧
  (balancedState conf s1 → balancedState conf s2) ∧
  (hasBadRef conf s2 → hasBadRef conf s1)

/-- A one-element data heap has exactly the protected pointers of its children. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "has_old_ptr_simp"]
theorem hasOldPtr_simp {α β γ : Type} (conf : Config α) (xs : List (HeapAddress β))
    (len : Nat) (payload : γ) :
    hasOldPtr conf [.dataElement xs len payload] = allOldPtrs conf xs := by
  funext ptr
  apply propext
  simp [hasOldPtr, allOldPtrs]

/-- Every heap element occupies at least one word. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "el_length_not_zero"]
theorem elLength_not_zero {α β : Type} (element : HeapElement α β) : elLength element ≠ 0 := by
  cases element
  all_goals simp [elLength]

/-- The encoded length of a cons is the head's length plus the tail's. -/
private theorem heapLength_cons {α β : Type} (element : HeapElement α β)
    (heap : List (HeapElement α β)) :
    heapLength (element :: heap) = elLength element + heapLength heap := by
  simp [heapLength, List.map_cons, List.sum_cons]

/-- Splitting a heap at the length of a prefix returns that prefix and the
rest. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "heap_split_length"]
theorem heapSplit_length {α β : Type} (h1 h2 : List (HeapElement α β)) :
    heapSplit (heapLength h1) (h1 ++ h2) = some (h1, h2) := by
  induction h1 with
  | nil =>
    cases h2 with
    | nil => simp [heapSplit, heapLength]
    | cons head tail => simp [heapSplit, heapLength]
  | cons head tail ih =>
    rw [List.cons_append, heapLength_cons]
    have positive : 0 < elLength head := Nat.pos_of_ne_zero (elLength_not_zero head)
    have fits : ¬ elLength head + heapLength tail < elLength head := by omega
    rw [heapSplit, if_neg (by omega : elLength head + heapLength tail ≠ 0), if_neg fits,
      Nat.add_sub_cancel_left, ih]
    rfl

/-- Restricting the empty heap yields the empty heap. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "heap_restrict_NIL"]
theorem heapRestrict_nil {α β : Type} (start finish : Nat) :
    heapRestrict start finish ([] : List (HeapElement α β)) = [] := by
  by_cases startZero : start = 0
  · by_cases finishZero : finish = 0
    · simp [heapRestrict, heapSegment, heapSplit, heapLength, startZero, finishZero]
    · simp [heapRestrict, heapSegment, heapSplit, heapLength, startZero, finishZero]
  · simp [heapRestrict, heapSegment, heapSplit, startZero]

/-- Translating the empty heap yields the empty heap. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "to_gen_heap_NIL"]
theorem toGenHeap_nil {α β γ : Type} (conf : Config γ) :
    toGenHeap conf ([] : List (HeapElement α β)) = [] := by
  simp [toGenHeap, toGenHeapList, heapRestrict_nil]

/-- Translating the empty heap list yields the empty heap list. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "to_gen_heap_list_NIL"]
theorem toGenHeapList_nil {α β γ : Type} (conf : Config γ) :
    toGenHeapList conf ([] : List (HeapElement α β)) = [] := rfl

/-- Looking up a translated heap list finds a data element exactly when the
source heap does. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml"
  "isSomeDataElement_to_gen_heap_element"]
theorem isSomeDataElement_toGenHeapElement {α β γ : Type} (conf : Config γ)
    (heap : List (HeapElement α β)) (ptr : Nat) :
    isSomeDataElement (heapLookup ptr (heap.map (toGenHeapElement conf))) ↔
      isSomeDataElement (heapLookup ptr heap) := by
  simpa [toGenHeapList] using isSomeDataElement_toGenHeapList conf heap ptr

/-- Translating a heap list preserves its encoded word length. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "heap_length_to_gen_heap_element"]
theorem heapLength_toGenHeapElement {α β γ : Type} (conf : Config γ)
    (heap : List (HeapElement α β)) :
    heapLength (heap.map (toGenHeapElement conf)) = heapLength heap := by
  simpa [toGenHeapList] using heapLength_toGenHeapList conf heap

/-- Translating one heap element preserves its encoded word length. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "el_length_to_gen_heap_element" 1775]
theorem elLength_toGenHeapElement {α β γ : Type} (conf : Config γ)
    (element : HeapElement α β) :
    elLength (toGenHeapElement conf element) = elLength element := by
  cases element
  all_goals simp [toGenHeapElement, elLength]

end Flapjack.Compiler.Backend.GenGcPartial
