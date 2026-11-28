module

public import Flapjack.Compiler.Backend.GcShared

@[expose] public section

/-! Heap lookup and filtering facts from `gc_sharedScript.sml`. -/
namespace Flapjack.Compiler.Backend
open Flapjack

@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "el_length_NOT_0"]
theorem elLength_ne_zero {α β : Type} (element : HeapElement α β) : elLength element ≠ 0 := by
  cases element
  all_goals simp [elLength]

@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "EVERY_isDataElement_IMP_LEMMA"]
theorem filter_isForwardPointer_eq_nil {α β : Type} (heap : List (HeapElement α β))
    (h : ∀ element ∈ heap, isDataElement element) : heap.filter isForwardPointer = [] := by
  induction heap with
  | nil => simp
  | cons head tail ih =>
    have hhead : isForwardPointer head = false := by
      obtain ⟨ptrs, len, data, rfl⟩ := h head (by simp)
      simp [isForwardPointer]
    simp only [List.filter_cons, hhead, Bool.false_eq_true, if_false]
    exact ih (fun element member => h element (by simp [member]))

@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "LESS_IMP_heap_lookup"]
theorem heapLookup_append_left {α β : Type} (xs : List (HeapElement α β)) (j : Nat)
    (ys : List (HeapElement α β)) (h : j < heapLength xs) :
    heapLookup j (xs ++ ys) = heapLookup j xs := by
  induction xs generalizing j with
  | nil => simp [heapLength] at h
  | cons head tail ih =>
    by_cases hzero : j = 0
    · simp [heapLookup, hzero]
    · by_cases hinside : j < elLength head
      · simp [heapLookup, hzero, hinside]
      · simp only [List.cons_append, heapLookup, hzero, hinside]
        have htail : j - elLength head < heapLength tail := by
          simp only [heapLength, List.map_cons, List.sum_cons] at h ⊢
          omega
        exact ih (j - elLength head) htail

@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "NOT_LESS_IMP_heap_lookup"]
theorem heapLookup_append_right {α β : Type} (xs : List (HeapElement α β)) (j : Nat)
    (ys : List (HeapElement α β)) (h : ¬ j < heapLength xs) :
    heapLookup j (xs ++ ys) = heapLookup (j - heapLength xs) ys := by
  induction xs generalizing j with
  | nil => simp [heapLength]
  | cons head tail ih =>
    have hge : elLength head + heapLength tail ≤ j := by
      simp only [heapLength, List.map_cons, List.sum_cons] at h ⊢
      omega
    have hpos := elLength_ge_one head
    have hnonzero : j ≠ 0 := by omega
    have houtside : ¬ j < elLength head := by omega
    simp only [List.cons_append, heapLookup, hnonzero, houtside]
    have hclock : j - heapLength (head :: tail) = j - elLength head - heapLength tail := by
      simp only [heapLength, List.map_cons, List.sum_cons]
      omega
    have htail : ¬ j - elLength head < heapLength tail := by omega
    rw [hclock]
    exact ih (j - elLength head) htail

@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "isSome_heap_looukp_IMP_APPEND"]
theorem isSomeDataElement_append {α β : Type} (xs : List (HeapElement α β)) (ptr : Nat)
    (ys : List (HeapElement α β)) (h : isSomeDataElement (heapLookup ptr xs)) :
    isSomeDataElement (heapLookup ptr (xs ++ ys)) := by
  obtain ⟨ptrs, len, data, heq⟩ := h
  have hless := heapLookup_less xs ptr (.dataElement ptrs len data) heq
  rw [heapLookup_append_left xs ptr ys hless]
  exact ⟨ptrs, len, data, heq⟩

end Flapjack.Compiler.Backend
