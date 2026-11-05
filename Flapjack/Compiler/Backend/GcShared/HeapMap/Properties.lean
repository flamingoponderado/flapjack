import Flapjack.Compiler.Backend.GcShared.HeapMap

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
      simp only [heapLookup, if_true, Option.some.injEq] at found
      subst head
      simp [heapMapLookup, FUPDATE]
    · by_cases inside : n < elLength head
      · simp [heapLookup, zero, inside] at found
      · have tailFound : heapLookup (n - elLength head) tail = some (.forwardPointer ptr value len) := by
          simpa only [heapLookup, zero, inside, if_false] using found
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

end Flapjack.Compiler.Backend
