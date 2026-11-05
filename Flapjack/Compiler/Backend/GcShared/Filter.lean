import Flapjack.Compiler.Backend.GcShared.Reachability
import Flapjack.Compiler.Backend.GcShared.HeapMap
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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

/-- Inserting a fresh address adds the length selected by that address. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_length_heap_filter_INSERT"]
theorem heapLength_heapFilter_insert {α β : Type} (heap : List (HeapElement α β))
    (e : Nat) (s : Nat → Prop) (fresh : ¬s e) :
    heapLength (heapFilter (fun p => p = e ∨ s p) heap) =
      heapLength (heapFilter (fun p => p = e) heap) + heapLength (heapFilter s heap) := by
  classical
  have aux : ∀ (heap : List (HeapElement α β)) offset,
      heapLength (heapFilterAux offset (fun p => p = e ∨ s p) heap) =
        heapLength (heapFilterAux offset (fun p => p = e) heap) +
          heapLength (heapFilterAux offset s heap) := by
    intro heap
    induction heap with
    | nil => intro offset; simp [heapFilterAux, heapLength]
    | cons head tail ih =>
      intro offset
      have recurrence := ih (offset + elLength head)
      simp only [heapLength] at recurrence
      by_cases atE : offset = e
      · subst offset
        simp [heapFilterAux, fresh, heapLength]
        omega
      · by_cases inS : s offset
        · simp [heapFilterAux, atE, inS, heapLength]
          omega
        · simpa [heapFilterAux, atE, inS, heapLength] using recurrence
  exact aux heap 0

/-- A finite selection's filtered length is the sum of its singleton filtered
lengths. This Flapjack helper supports the collector's bijection proof. -/
theorem heapLength_heapFilter_finset {α β : Type} (heap : List (HeapElement α β))
    (s : Finset Nat) :
    heapLength (heapFilter (fun p => p ∈ s) heap) =
      s.sum (fun p => heapLength (heapFilter (fun q => q = p) heap)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [heapFilter_empty, heapLength]
  | @insert e s fresh ih =>
    have selector : (fun p => p ∈ insert e s) = (fun p => p = e ∨ p ∈ s) := by
      funext p
      exact propext (by simp)
    rw [selector, heapLength_heapFilter_insert heap e (fun p => p ∈ s) fresh, ih,
      Finset.sum_insert fresh]

/-- A bijection between selected data elements of equal lengths preserves the
filtered heap length. The first existential payload is an independent,
unused type variable in the inferred HOL statement. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_length_heap_filter_eq"]
theorem heapLength_heapFilter_eq {α β γ δ : Type} (s t : Set Nat) (f : Nat → Nat)
    (heap : List (HeapElement α β)) (heap2 : List (HeapElement γ β))
    (bijective : Set.BijOn f s t) (finiteS : s.Finite) (finiteT : t.Finite)
    (matching : ∀ i ∈ s, ∃ (xs : List (HeapAddress α)) (xs2 : List (HeapAddress γ))
        (len : Nat) (_unused : δ) (data : β),
      heapLookup i heap = some (.dataElement xs len data) ∧
      heapLookup (f i) heap2 = some (.dataElement xs2 len data)) :
    heapLength (heapFilter t heap2) = heapLength (heapFilter s heap) := by
  classical
  have sourceSelector : (fun p => p ∈ finiteS.toFinset) = s := by
    funext p
    exact propext finiteS.mem_toFinset
  have targetSelector : (fun p => p ∈ finiteT.toFinset) = t := by
    funext p
    exact propext finiteT.mem_toFinset
  have sourceSum := heapLength_heapFilter_finset heap finiteS.toFinset
  have targetSum := heapLength_heapFilter_finset heap2 finiteT.toFinset
  rw [sourceSelector] at sourceSum
  rw [targetSelector] at targetSum
  rw [targetSum, sourceSum]
  symm
  apply Finset.sum_bij (fun i _ => f i)
  · intro i member
    exact finiteT.mem_toFinset.mpr (bijective.1 (finiteS.mem_toFinset.mp member))
  · intro i hi j hj eq
    exact bijective.2.1 (finiteS.mem_toFinset.mp hi) (finiteS.mem_toFinset.mp hj) eq
  · intro j member
    obtain ⟨i, hi, eq⟩ := bijective.2.2 (finiteT.mem_toFinset.mp member)
    exact ⟨i, finiteS.mem_toFinset.mpr hi, eq⟩
  · intro i member
    obtain ⟨xs, xs2, len, _, data, sourceLookup, targetLookup⟩ := matching i (finiteS.mem_toFinset.mp member)
    rw [heapLookup_imp_heapFilter heap i _ sourceLookup, heapLookup_imp_heapFilter heap2 (f i) _ targetLookup]
    simp [heapLength, elLength]

end Flapjack.Compiler.Backend
