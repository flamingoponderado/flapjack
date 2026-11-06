import Flapjack.Compiler.Backend.GcShared
import Flapjack.HolArb

/-! The abstract copying collector from `copying_gcScript.sml`. -/
namespace Flapjack.Compiler.Backend.CopyingGc
open Flapjack

/-- Move one root, recording a forwarding pointer for a freshly copied
element. A failed lookup returns HOL's arbitrary address and false. -/
@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "gc_move_def"]
noncomputable def gcMove {α β : Type} :
    HeapAddress α × List (HeapElement α β) × Nat × Nat × List (HeapElement α β) × Bool × Nat →
      HeapAddress α × List (HeapElement α β) × Nat × Nat × List (HeapElement α β) × Bool
  | (.data d, copied, a, n, heap, ok, _) => (.data d, copied, a, n, heap, ok)
  | (.pointer ptr d, copied, a, n, heap, ok, limit) =>
      match heapLookup ptr heap with
      | some (.dataElement xs len payload) =>
          let ok := ok && decide (len + 1 ≤ n) && decide (a + n = limit)
          let (heap, ok) := gcForwardPtr ptr heap a d ok
          (.pointer a d, copied ++ [.dataElement xs len payload], a + (len + 1), n - (len + 1), heap, ok)
      | some (.forwardPointer newPtr _ _) => (.pointer newPtr d, copied, a, n, heap, ok)
      | _ => (@holArb (HeapAddress α) ⟨.data d⟩, copied, a, n, heap, false)

/-- Move each root in order, threading the heap and allocation state. -/
@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "gc_move_list_def"]
noncomputable def gcMoveList {α β : Type} :
    List (HeapAddress α) × List (HeapElement α β) × Nat × Nat × List (HeapElement α β) × Bool × Nat →
      List (HeapAddress α) × List (HeapElement α β) × Nat × Nat × List (HeapElement α β) × Bool
  | ([], copied, a, n, heap, ok, _) => ([], copied, a, n, heap, ok)
  | (root :: roots, copied, a, n, heap, ok, limit) =>
      let (root, copied, a, n, heap, ok) := gcMove (root, copied, a, n, heap, ok, limit)
      let (roots, copied, a, n, heap, ok) := gcMoveList (roots, copied, a, n, heap, ok, limit)
      (root :: roots, copied, a, n, heap, ok)
termination_by input => input.1.length

open Classical in
/-- Scan copied elements until no unscanned elements remain, following the
original heap-length termination measure. -/
@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "gc_move_loop_def"]
noncomputable def gcMoveLoop {α β : Type} :
    List (HeapElement α β) × List (HeapElement α β) × Nat × Nat × List (HeapElement α β) × Bool × Nat →
      List (HeapElement α β) × Nat × Nat × List (HeapElement α β) × Bool
  | (scanned, [], a, n, heap, ok, _) => (scanned, a, n, heap, ok)
  | (scanned, h :: pending, a, n, heap, ok, limit) =>
      if limit < heapLength (scanned ++ h :: pending) then (scanned, a, n, heap, false)
      else match _heq : h with
      | .dataElement xs len payload =>
          let (xs, pending', a, n, heap, ok) := gcMoveList (xs, h :: pending, a, n, heap, ok, limit)
          let ok := ok && decide (pending' ≠ []) && decide (pending'.head? = some h)
          gcMoveLoop (scanned ++ [.dataElement xs len payload], pending'.drop 1, a, n, heap, ok, limit)
      | _ => (scanned, a, n, heap, false)
termination_by input => input.2.2.2.2.2.2 - heapLength input.1
decreasing_by
  simp_all [heapLength, List.map_append, List.sum_append, elLength]
  omega

/-- Move the roots and scan their reachable copied heap. -/
@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "full_gc_def"]
noncomputable def fullGc {α β : Type} :
    List (HeapAddress α) × List (HeapElement α β) × Nat →
      List (HeapAddress α) × List (HeapElement α β) × Nat × Bool
  | (roots, heap, limit) =>
      let c0 := decide (heapLength heap = limit)
      let (roots, pending, a, n, heap, ok) := gcMoveList (roots, [], 0, limit, heap, true, limit)
      let (heap, a, n, temporary, ok) := gcMoveLoop ([], pending, a, n, heap, ok, limit)
      let ok := ok && decide (a = heapLength heap) && decide (heapLength temporary = limit) &&
        c0 && decide (n = limit - a) && decide (a ≤ limit)
      (roots, heap, a, ok)

end Flapjack.Compiler.Backend.CopyingGc
