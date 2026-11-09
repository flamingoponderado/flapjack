module

public import Flapjack.Compiler.Backend.GcShared.State

@[expose] public section

/-! Abstract major generational collector. -/
namespace Flapjack.Compiler.Backend.GenGc

/-- Major collection limit and reference classification. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "gen_gc_conf"]
structure Config (β : Type) where
  limit : Nat
  isRef : β → Bool

/-- Move one root, placing reference objects at the right of the heap. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "gc_move_def"]
def gcMove {α β : Type} (conf : Config β) (state : GcState α β) :
    HeapAddress α → HeapAddress α × GcState α β
  | .data d => (.data d, state)
  | .pointer ptr d =>
    match heapLookup ptr state.heap with
    | some (.forwardPointer newPtr _ _) => (.pointer newPtr d, state)
    | some (.dataElement xs len payload) =>
      let ok := state.ok && decide (len + 1 ≤ state.n)
      let n := state.n - (len + 1)
      if conf.isRef payload then
        let (heap, ok) := gcForwardPtr ptr state.heap (state.a + n) d ok
        (.pointer (state.a + n) d, { state with r4 := .dataElement xs len payload :: state.r4, n := n, heap := heap, ok := ok })
      else
        let (heap, ok) := gcForwardPtr ptr state.heap state.a d ok
        (.pointer state.a d, { state with h2 := state.h2 ++ [.dataElement xs len payload], n := n, a := state.a + len + 1, heap := heap, ok := ok })
    | _ => (.pointer ptr d, { state with ok := false })

/-- Move the roots from left to right, threading the collector state. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "gc_move_list_def"]
def gcMoveList {α β : Type} (conf : Config β) :
    GcState α β → List (HeapAddress α) → List (HeapAddress α) × GcState α β
  | state, [] => ([], state)
  | state, root :: roots =>
    let (root1, state1) := gcMove conf state root
    let (roots1, state2) := gcMoveList conf state1 roots
    (root1 :: roots1, state2)

/-- Moving roots leaves the scanned left heap unchanged. This is a local
termination invariant, not a separate HOL declaration. -/
theorem gcMove_h1 {α β : Type} (conf : Config β) (state : GcState α β) (root : HeapAddress α) :
    (gcMove conf state root).2.h1 = state.h1 := by
  cases root with
  | data d => rfl
  | pointer ptr d =>
    cases h : heapLookup ptr state.heap with
    | none => simp [gcMove, h]
    | some element =>
      cases element <;> simp [gcMove, h]
      split <;> rfl

/-- The root-list traversal preserves the scanned left heap. -/
theorem gcMoveList_h1 {α β : Type} (conf : Config β) (state : GcState α β)
    (roots : List (HeapAddress α)) : (gcMoveList conf state roots).2.h1 = state.h1 := by
  induction roots generalizing state with
  | nil => rfl
  | cons root roots ih =>
    simp only [gcMoveList]
    generalize result : gcMove conf state root = moved
    rcases moved with ⟨root1, state1⟩
    have same := gcMove_h1 conf state root
    rw [result] at same
    exact (ih state1).trans same

open Classical in
/-- Scan the copied data objects, using the source's heap-length measure. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "gc_move_data_def"]
noncomputable def gcMoveData {α β : Type} (conf : Config β) (state : GcState α β) : GcState α β :=
  match state.h2 with
  | [] => state
  | head :: tail =>
    if conf.limit < heapLength (state.h1 ++ head :: tail) then { state with ok := false }
    else match _headEq : head with
      | .dataElement roots len payload =>
        match _moveEq : gcMoveList conf state roots with
        | (roots1, state1) =>
          let ok := state1.ok && decide (state1.h2 ≠ []) && decide (state1.h2.head? = some head)
          gcMoveData conf { state1 with h1 := state1.h1 ++ [.dataElement roots1 len payload], h2 := state1.h2.drop 1, ok := ok }
      | _ => { state with ok := false }
termination_by conf.limit - heapLength state.h1
decreasing_by
  have same := gcMoveList_h1 conf state roots
  simp_all [heapLength, elLength, List.map_append, List.sum_append]
  omega

/-- Scan reference objects accumulated on the right. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "gc_move_refs_def"]
def gcMoveRefs {α β : Type} (conf : Config β) (state : GcState α β) : GcState α β :=
  match _refsEq : state.r2 with
  | [] => { state with r3 := [], r1 := state.r3 ++ state.r1 }
  | head :: tail =>
    match _headEq : head with
    | .dataElement roots len payload =>
      let (roots1, state1) := gcMoveList conf state roots
      gcMoveRefs conf { state1 with r2 := tail, r3 := state1.r3 ++ [.dataElement roots1 len payload] }
    | _ => { state with ok := false }
termination_by heapLength state.r2
decreasing_by
  simp_all [heapLength, elLength]

open Classical in
/-- Alternate between data and reference scans for the source clock. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "gc_move_loop_def"]
noncomputable def gcMoveLoop {α β : Type} (conf : Config β) (state : GcState α β) (clock : Nat) : GcState α β :=
    match state.r4 with
    | [] =>
      match state.h2 with
      | [] => state
      | _ :: _ =>
        let state1 := gcMoveData conf state
        if clock = 0 then { state1 with ok := false } else gcMoveLoop conf state1 (clock - 1)
    | _ :: _ =>
      let state1 := gcMoveRefs conf { state with r2 := state.r4, r4 := [] }
      if clock = 0 then { state1 with ok := false } else gcMoveLoop conf state1 (clock - 1)
termination_by clock
decreasing_by all_goals omega

open Classical in
/-- Major collection starts with an empty state, then moves and scans roots. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "gen_gc_def"]
noncomputable def genGc {α β : Type} (conf : Config β)
    (input : List (HeapAddress α) × List (HeapElement α β)) : List (HeapAddress α) × GcState α β :=
  let (roots, heap) := input
  let state := { emptyGcState with heap := heap, n := conf.limit, ok := decide (heapLength heap = conf.limit) }
  let (roots1, state1) := gcMoveList conf state roots
  (roots1, gcMoveLoop conf state1 conf.limit)

end Flapjack.Compiler.Backend.GenGc
