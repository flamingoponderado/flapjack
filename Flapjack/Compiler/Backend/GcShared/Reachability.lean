import Flapjack.Compiler.Backend.GcShared
import Mathlib.Logic.Relation

/-! Heap reachability and filtering used by abstract collector correctness. -/
namespace Flapjack.Compiler.Backend

/-- An edge follows a pointer stored in a data element. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "gc_edge_def"]
def gcEdge {α β : Type} (heap : List (HeapElement α β)) (source target : Nat) : Prop :=
  ∃ roots len payload value,
    heapLookup source heap = some (.dataElement roots len payload) ∧ .pointer target value ∈ roots

/-- Addresses reachable from a pointer root by zero or more heap edges. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "reachable_addresses_def"]
def reachableAddresses {α β γ : Type} (roots : List (HeapAddress α)) (heap : List (HeapElement β γ))
    (target : Nat) : Prop :=
  ∃ value source, .pointer source value ∈ roots ∧ Relation.ReflTransGen (gcEdge heap) source target

open Classical in
/-- Retain elements whose starting addresses satisfy the supplied set. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_filter_aux_def"]
noncomputable def heapFilterAux {α β : Type} (offset : Nat) (selected : Nat → Prop) :
    List (HeapElement α β) → List (HeapElement α β)
  | [] => []
  | head :: tail => (if selected offset then [head] else []) ++ heapFilterAux (offset + elLength head) selected tail

open Classical in
/-- Filter a heap by element starting addresses. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_filter_def"]
noncomputable def heapFilter {α β : Type} (selected : Nat → Prop) (heap : List (HeapElement α β)) :
    List (HeapElement α β) := heapFilterAux 0 selected heap

/-- Filtering by the empty set produces an empty heap. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_filter_EMPTY"]
theorem heapFilter_empty {α β : Type} (heap : List (HeapElement α β)) :
    heapFilter (fun _ => False) heap = [] := by
  classical
  have auxiliary : ∀ offset, heapFilterAux offset (fun _ => False) heap = [] := by
    induction heap with
    | nil => intro offset; rfl
    | cons head tail ih => intro offset; simp [heapFilterAux, ih]
  exact auxiliary 0

end Flapjack.Compiler.Backend
