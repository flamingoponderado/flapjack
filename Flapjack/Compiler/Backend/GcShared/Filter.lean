import Flapjack.Compiler.Backend.GcShared.Reachability
import Flapjack.Compiler.Backend.GcShared.HeapMap

/-! Heap filtering by element starting addresses. -/
namespace Flapjack.Compiler.Backend

private theorem heapFilterAux_of_covers {α β : Type} (heap : List (HeapElement α β))
    (offset : Nat) (selected : Nat → Prop)
    (covers : ∀ p, heapAddresses offset heap p → selected p) :
    heapFilterAux offset selected heap = heap := by
  classical
  induction heap generalizing offset with
  | nil => rfl
  | cons head tail ih =>
    have atHead : selected offset := covers offset (by simp [heapAddresses])
    have coversTail : ∀ p, heapAddresses (offset + elLength head) tail p → selected p := by
      intro p member
      exact covers p (by simp [heapAddresses, member])
    simp [heapFilterAux, atHead, ih (offset + elLength head) coversTail]

/-- Filtering by a set containing all element addresses retains the heap. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_filter_aux_heap_addresses_UNION"]
theorem heapFilterAux_addresses_union {α β : Type} (xs : List (HeapElement α β)) (n : Nat)
    (s : Nat → Prop) :
    heapFilterAux n (fun p => heapAddresses n xs p ∨ s p) xs = xs := by
  apply heapFilterAux_of_covers
  intro p member
  exact Or.inl member

/-- Filtering by every element address preserves the heap's total length. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_length_heap_filter"]
theorem heapLength_heapFilter_addresses {α β : Type} (heap : List (HeapElement α β)) :
    heapLength (heapFilter (heapAddresses 0 heap) heap) = heapLength heap := by
  have all : heapFilterAux 0 (heapAddresses 0 heap) heap = heap := by
    apply heapFilterAux_of_covers
    intro p member
    exact member
  simp [heapFilter, all]

/-- Heap filtering distributes over concatenation, advancing the base by the
first heap's word length. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_filter_aux_APPEND"]
theorem heapFilterAux_append {α β : Type} (xs ys : List (HeapElement α β)) (n : Nat)
    (s : Nat → Prop) :
    heapFilterAux n s (xs ++ ys) = heapFilterAux n s xs ++ heapFilterAux (n + heapLength xs) s ys := by
  classical
  induction xs generalizing n with
  | nil => simp [heapFilterAux, heapLength]
  | cons head tail ih =>
    simp [heapFilterAux, heapLength, ih, List.append_assoc, Nat.add_assoc]

private theorem heapFilterAux_of_disjoint {α β : Type} (heap : List (HeapElement α β))
    (offset : Nat) (selected : Nat → Prop)
    (disjoint : ∀ p, heapAddresses offset heap p → ¬selected p) :
    heapFilterAux offset selected heap = [] := by
  classical
  induction heap generalizing offset with
  | nil => rfl
  | cons head tail ih =>
    have notHead : ¬ selected offset := disjoint offset (by simp [heapAddresses])
    have disjointTail : ∀ p, heapAddresses (offset + elLength head) tail p → ¬selected p := by
      intro p member
      exact disjoint p (by simp [heapAddresses, member])
    simp [heapFilterAux, notHead, ih (offset + elLength head) disjointTail]

/-- Filtering a heap by the address of a successful lookup retains exactly
the element returned by that lookup. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_lookup_IMP_heap_filter"]
theorem heapLookup_imp_heapFilter {α β : Type} (heap : List (HeapElement α β)) (e : Nat)
    (x : HeapElement α β) (found : heapLookup e heap = some x) :
    heapFilter (fun p => p = e) heap = [x] := by
  obtain ⟨before, after, rfl, rfl⟩ := heapLookup_split heap e x found
  have emptyBefore : heapFilterAux 0 (fun p => p = heapLength before) before = [] := by
    apply heapFilterAux_of_disjoint
    intro p member eq
    have upper := heapAddresses_less_heapLength before 0 p member
    omega
  have emptyAfter : heapFilterAux (heapLength before + elLength x)
      (fun p => p = heapLength before) after = [] := by
    apply heapFilterAux_of_disjoint
    intro p member eq
    have lower := heapAddresses_base_le after (heapLength before + elLength x) p member
    have positive : 0 < elLength x := by cases x <;> simp [elLength]
    omega
  simp [heapFilter, heapFilterAux_append, heapFilterAux, emptyBefore, emptyAfter]

end Flapjack.Compiler.Backend
