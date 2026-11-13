module

public import Flapjack.Compiler.Backend.GcShared
public import Flapjack.Compiler.Backend.GcShared.HeapMap

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
          simp only [heapLookup, zero, ite_false, inside, under, ite_true, ih, heapLength, below]
        · have under : ¬offset < elLength head + (tail.map elLength).sum := by
            intro h; exact below (relation.mp h)
          simp only [heapLookup, zero, ite_false, inside, under, ih, heapLength, below, Nat.sub_sub]

/-- Every successful lookup is at an element starting address. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "heap_lookup_IMP_heap_addresses"]
theorem heapLookup_imp_heapAddresses {α β : Type} (xs : List (HeapElement α β)) (n : Nat)
    (x : HeapElement α β) (found : heapLookup n xs = some x) : heapAddresses 0 xs n := by
  obtain ⟨before, after, rfl, rfl⟩ := heapLookup_split xs n x found
  rw [heapAddresses_append]
  simp [heapAddresses]

end Flapjack.Compiler.Backend.GenGc
