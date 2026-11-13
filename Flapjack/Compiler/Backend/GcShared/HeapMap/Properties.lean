module

public import Flapjack.Compiler.Backend.GcShared.HeapMap
public import Flapjack.FiniteMap.MapKeys

@[expose] public section

/-! Lookup and domain properties of the collector forwarding map. -/
namespace Flapjack.Compiler.Backend
open Flapjack

private theorem heapMapLookup_below {α β : Type} (heap : List (HeapElement α β)) (base key : Nat)
    (below : key < base) : heapMapLookup base heap key = none := by
  induction heap generalizing base with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | unused len =>
      exact ih (base + elLength (.unused len)) (by simp [elLength]; omega)
    | dataElement pointers len payload =>
      exact ih (base + elLength (.dataElement pointers len payload)) (by simp [elLength]; omega)
    | forwardPointer ptr value len =>
      simp only [heapMapLookup, FUPDATE]
      have ne : base ≠ key := by omega
      simp [ne, ih (base + len + 1) (by omega)]

/-- An entry in a forwarding map cannot precede its starting offset. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "IN_heap_map_IMP"
  (fmap_as_finite_support_result_observations := [heapMap])]
theorem in_heapMap_imp {α β : Type} (heap : List (HeapElement α β)) (n k : Nat)
    (member : (heapMap k heap).lookup n ≠ none) : k ≤ n := by
  by_cases below : n < k
  · exfalso
    apply member
    rw [holFmapAsFiniteSupportResultWitness_heapMap]
    exact heapMapLookup_below heap k n below
  · omega

private theorem heapLookup_flookup_aux {α β : Type} (heap : List (HeapElement α β))
    (n base ptr len : Nat) (value : α)
    (found : heapLookup n heap = some (.forwardPointer ptr value len)) :
    heapMapLookup base heap (n + base) = some ptr := by
  induction heap generalizing n base with
  | nil => simp [heapLookup] at found
  | cons head tail ih =>
    by_cases zero : n = 0
    · subst n
      simp only [heapLookup, ite_true, Option.some.injEq] at found
      subst head
      simp [heapMapLookup, FUPDATE]
    · by_cases inside : n < elLength head
      · simp [heapLookup, zero, inside] at found
      · have tailFound : heapLookup (n - elLength head) tail = some (.forwardPointer ptr value len) := by
          simpa only [heapLookup, zero, inside, ite_false] using found
        have next := ih (n - elLength head) (base + elLength head) tailFound
        have sumEq : n - elLength head + (base + elLength head) = n + base := by omega
        rw [sumEq] at next
        cases head with
        | unused size => simpa [heapMapLookup, elLength] using next
        | dataElement children size payload => simpa [heapMapLookup, elLength] using next
        | forwardPointer target payload size =>
          have ne : base ≠ n + base := by omega
          simpa [heapMapLookup, elLength, FUPDATE, ne, zero, Nat.add_assoc] using next

/-- A forwarding-pointer lookup yields the matching map entry. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_lookup_FLOOKUP"
  (fmap_as_finite_support_result_observations := [heapMap])]
theorem heapLookup_flookup {α β : Type} (heap : List (HeapElement α β))
    (n ptr len : Nat) (value : α)
    (found : heapLookup n heap = some (.forwardPointer ptr value len)) :
    (heapMap 0 heap).lookup n = some ptr := by
  rw [holFmapAsFiniteSupportResultWitness_heapMap]
  simpa using heapLookup_flookup_aux heap n 0 ptr len value found

/-- A heap with no forwarding pointers has an empty forwarding-map domain. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_map_EMPTY"
  (fmap_as_finite_support_result_observations := [heapMap])]
theorem heapMap_empty {α β : Type} (xs : List (HeapElement α β)) (n : Nat)
    (noForward : xs.filter isForwardPointer = []) :
    (fun key => (heapMap n xs).lookup key ≠ none) = (fun _ => False) := by
  have emptyLookup : ∀ (xs : List (HeapElement α β)) (base key : Nat),
      xs.filter isForwardPointer = [] → heapMapLookup base xs key = none := by
    intro heap
    induction heap with
    | nil => intros; rfl
    | cons head tail ih =>
      intro base key noForward
      cases head with
      | unused len =>
        simp only [List.filter_cons, isForwardPointer, Bool.false_eq_true, ↓reduceIte] at noForward
        exact ih (base + elLength (.unused len)) key noForward
      | forwardPointer ptr value len => simp [isForwardPointer] at noForward
      | dataElement roots len data =>
        simp only [List.filter_cons, isForwardPointer, Bool.false_eq_true, ↓reduceIte] at noForward
        exact ih (base + elLength (.dataElement roots len data)) key noForward
  funext key
  rw [holFmapAsFiniteSupportResultWitness_heapMap, emptyLookup xs n key noForward]
  simp

private theorem heapMapLookup_replace_data {α β : Type} (before suffix : List (HeapElement α β))
    (base key target len : Nat) (roots : List (HeapAddress α)) (data : β) (value : α) :
    heapMapLookup base (before ++ .forwardPointer target value len :: suffix) key =
      FUPDATE (heapMapLookup base (before ++ .dataElement roots len data :: suffix))
        (base + heapLength before, target) key := by
  induction before generalizing base with
  | nil => simp [heapMapLookup, heapLength, elLength, Nat.add_assoc]
  | cons head tail ih =>
    cases head with
    | unused size =>
      simpa [heapMapLookup, heapLength, elLength, Nat.add_assoc] using ih (base + (size + 1))
    | dataElement children size payload =>
      simpa [heapMapLookup, heapLength, elLength, Nat.add_assoc] using ih (base + (size + 1))
    | forwardPointer old ptr size =>
      by_cases atBase : key = base
      · simp [heapMapLookup, heapLength, elLength, FUPDATE, atBase, Nat.add_assoc]
      · have recEq := ih (base + (size + 1))
        have ne : base ≠ key := Ne.symm atBase
        simpa [heapMapLookup, heapLength, elLength, FUPDATE, ne, Nat.add_assoc] using recEq

/-- Replacing a data element by a same-sized forwarding pointer updates its
starting-address entry and leaves every other forwarding-map lookup unchanged.
This Flapjack lemma isolates a step of the copying collector proof. -/
theorem heapMap_replace_data {α β : Type} (before suffix : List (HeapElement α β))
    (target len : Nat) (roots : List (HeapAddress α)) (data : β) (value : α) :
    heapMap 0 (before ++ .forwardPointer target value len :: suffix) =
      (heapMap 0 (before ++ .dataElement roots len data :: suffix)).update
        (heapLength before, target) := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  simp only [holFmapAsFiniteSupportResultWitness_heapMap, HolFiniteMapExact.lookup_update]
  have lookupEq : (heapMap 0 (before ++ .dataElement roots len data :: suffix)).lookup =
      heapMapLookup 0 (before ++ .dataElement roots len data :: suffix) := by
    funext address
    exact holFmapAsFiniteSupportResultWitness_heapMap 0 _ address
  rw [lookupEq]
  simpa using heapMapLookup_replace_data before suffix 0 key target len roots data value

private theorem heapMapLookup_data_address {α β : Type} (before suffix : List (HeapElement α β))
    (base len : Nat) (roots : List (HeapAddress α)) (data : β) :
    heapMapLookup base (before ++ .dataElement roots len data :: suffix)
      (base + heapLength before) = none := by
  induction before generalizing base with
  | nil =>
    simp only [List.nil_append, heapMapLookup, heapLength, List.map_nil, List.sum_nil, Nat.add_zero]
    exact heapMapLookup_below suffix (base + elLength (.dataElement roots len data)) base (by
      simp [elLength])
  | cons head tail ih =>
    cases head with
    | unused size =>
      simpa [heapMapLookup, heapLength, elLength, Nat.add_assoc] using ih (base + (size + 1))
    | dataElement children size payload =>
      simpa [heapMapLookup, heapLength, elLength, Nat.add_assoc] using ih (base + (size + 1))
    | forwardPointer ptr value size =>
      have next := ih (base + (size + 1))
      simpa [heapMapLookup, heapLength, elLength, FUPDATE, Nat.add_assoc] using next

/-- A data element's starting address is absent from the forwarding map. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "NOT_IN_heap_map"
  (fmap_as_finite_support_result_observations := [heapMap])]
theorem not_in_heapMap {α β : Type} (ha hb : List (HeapElement α β))
    (ys : List (HeapAddress α)) (len : Nat) (data : β) :
    (heapMap 0 (ha ++ .dataElement ys len data :: hb)).lookup (heapLength ha) = none := by
  rw [holFmapAsFiniteSupportResultWitness_heapMap]
  simpa using heapMapLookup_data_address ha hb 0 len ys data

end Flapjack.Compiler.Backend
