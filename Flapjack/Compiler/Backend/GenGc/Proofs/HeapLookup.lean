module

public import Flapjack.Compiler.Backend.GcShared
public import Flapjack.Compiler.Backend.GcShared.HeapMap
public import Flapjack.Compiler.Backend.GcShared.Reachability
public import Flapjack.Compiler.Backend.GcShared.Reachability

@[expose] public section

/-! Heap lookup over concatenation in the generational collector. -/
namespace Flapjack.Compiler.Backend.GenGc
open Flapjack Flapjack.Compiler.Backend

/-- A lookup selects the side containing its heap-word offset. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "heap_lookup_APPEND"]
theorem heapLookup_append {α β : Type} (offset : Nat) (first second : List (HeapElement α β)) :
    heapLookup offset (first ++ second) =
      if offset < heapLength first then heapLookup offset first else heapLookup (offset - heapLength first) second := by
  induction first generalizing offset with
  | nil => simp [heapLength]
  | cons head tail ih =>
    simp only [List.cons_append, heapLength, List.map_cons, List.sum_cons]
    by_cases zero : offset = 0
    · subst offset
      have positive : 0 < elLength head := by cases head <;> simp [elLength]
      have under : 0 < elLength head + (tail.map elLength).sum := by omega
      simp [heapLookup, under]
    · by_cases inside : offset < elLength head
      · have under : offset < elLength head + (tail.map elLength).sum := by omega
        simp [heapLookup, zero, inside, under]
      · have relation : offset < elLength head + (tail.map elLength).sum ↔
            offset - elLength head < (tail.map elLength).sum := by omega
        by_cases below : offset - elLength head < (tail.map elLength).sum
        · have under : offset < elLength head + (tail.map elLength).sum := relation.mpr below
          simp only [heapLookup, zero, if_false, inside, under, if_true, ih, heapLength, below]
        · have under : ¬offset < elLength head + (tail.map elLength).sum := by
            intro h; exact below (relation.mp h)
          simp only [heapLookup, zero, if_false, inside, under, ih, heapLength, below, Nat.sub_sub]

/-- Every successful lookup is at an element starting address. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "heap_lookup_IMP_heap_addresses"]
theorem heapLookup_imp_heapAddresses {α β : Type} (xs : List (HeapElement α β)) (n : Nat)
    (x : HeapElement α β) (found : heapLookup n xs = some x) : heapAddresses 0 xs n := by
  obtain ⟨before, after, rfl, rfl⟩ := heapLookup_split xs n x found
  rw [heapAddresses_append]
  simp [heapAddresses]

/-- Original gen_gcScript `heap_lookup_EXTEND`: the same statement as the
    gc_shared rule, carried under the gen_gc HOL name. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "heap_lookup_EXTEND"]
theorem heapLookup_extend' {α β : Type} (xs : List (HeapElement α β)) (n : Nat)
    (ys : List (HeapElement α β)) (x : HeapElement α β) (found : heapLookup n xs = some x) :
    heapLookup n (xs ++ ys) = some x := by
  have under : n < heapLength xs := heapLookup_less xs n x found
  rw [heapLookup_append]
  simp [under, found]

/-- Original `LESS_IMP_heap_lookup`: a lookup below the prefix length stays in
    the prefix. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "LESS_IMP_heap_lookup"]
theorem heapLookup_less_append {α β : Type} (xs : List (HeapElement α β)) (j : Nat)
    (ys : List (HeapElement α β)) (under : j < heapLength xs) :
    heapLookup j (xs ++ ys) = heapLookup j xs := by
  rw [heapLookup_append]
  simp [under]

/-- Original `heap_lookup_IMP_MEM`: a successful lookup returns a member. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "heap_lookup_IMP_MEM"]
theorem heapLookup_mem {α β : Type} (xs : List (HeapElement α β)) (n : Nat)
    (y : HeapElement α β) (found : heapLookup n xs = some y) : y ∈ xs := by
  obtain ⟨before, after, rfl, _⟩ := heapLookup_split xs n y found
  simp

/-- Original `heap_lookup_LENGTH`: the boundary after a prefix is its next
    element. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "heap_lookup_LENGTH"]
theorem heapLookup_length_append {α β : Type} (xs : List (HeapElement α β))
    (x : HeapElement α β) (ys : List (HeapElement α β)) (l : Nat)
    (same : heapLength xs = l) : heapLookup l (xs ++ x :: ys) = some x := by
  subst l
  rw [heapLookup_append]
  simp only [Nat.lt_irrefl, if_false, Nat.sub_self]
  simp [heapLookup]

/-- Original `IMP_reachable_addresses`: a pointer stored in a reachable data
    element is itself reachable. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "IMP_reachable_addresses"]
theorem impReachableAddresses {α β γ : Type} (roots0 : List (HeapAddress α))
    (heap0 : List (HeapElement β γ)) (i ptr : Nat) (u : β) (xs : List (HeapAddress β))
    (l : Nat) (d : γ)
    (h : reachableAddresses roots0 heap0 i ∧ HeapAddress.pointer ptr u ∈ xs ∧
      heapLookup i heap0 = some (HeapElement.dataElement xs l d)) :
    reachableAddresses roots0 heap0 ptr := by
  obtain ⟨reach, mem, found⟩ := h
  obtain ⟨value, source, root, path⟩ := reach
  exact ⟨value, source, root,
    Relation.ReflTransGen.trans path (Relation.ReflTransGen.single ⟨xs, l, d, u, found, mem⟩)⟩

/-- Original `gc_forward_ptr_ok`: a successful forwarding-pointer write can only
    happen when the incoming status is true. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "gc_forward_ptr_ok"]
theorem gcForwardPtr_ok {α β : Type} (heap : List (HeapElement α β)) (n : Nat)
    (a : Nat) (d : α) (c : Bool) (x : List (HeapElement α β)) :
    gcForwardPtr n heap a d c = (x, true) → c = true := by
  induction heap generalizing n x with
  | nil =>
      intro h
      simp [gcForwardPtr] at h
  | cons head tail ih =>
      intro h
      simp only [gcForwardPtr] at h
      split at h
      · have both := (Prod.mk.inj h).2
        rw [Bool.and_eq_true] at both
        exact both.2
      · split at h
        · exact absurd (Prod.mk.inj h).2 (by simp)
        · cases hrec : gcForwardPtr (n - elLength head) tail a d c with
          | mk ys ok =>
              rw [hrec] at h
              have flag : ok = true := (Prod.mk.inj h).2
              subst ok
              exact ih (n - elLength head) ys hrec

/-- Original `heap_lookup_LENGTH`: the element starting at the prefix length. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "heap_lookup_LENGTH"]
theorem heapLookup_length {α β : Type} (xs : List (HeapElement α β)) (x : HeapElement α β)
    (ys : List (HeapElement α β)) (l : Nat) (h : heapLength xs = l) :
    heapLookup l (xs ++ x :: ys) = some x := by
  induction xs generalizing l with
  | nil =>
    simp only [heapLength, List.nil_append] at h ⊢
    subst h
    simp [heapLookup]
  | cons head tail ih =>
    rw [heapLookup_append]
    have hl : heapLength (head :: tail) = l := by
      simp only [heapLength, List.map_cons, List.sum_cons] at h ⊢
      exact h
    have notBelow : ¬ l < heapLength (head :: tail) := by
      rw [hl]
      omega
    have zero : l - heapLength (head :: tail) = 0 := by
      rw [hl]
      omega
    simp only [notBelow, if_false, zero]
    simp [heapLookup]

end Flapjack.Compiler.Backend.GenGc
