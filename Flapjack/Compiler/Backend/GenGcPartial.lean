import Flapjack.Compiler.Backend.GcShared.State

/-! Abstract minor generational collector. -/
namespace Flapjack.Compiler.Backend.GenGcPartial

/-- Minor collection bounds and reference classification. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gen_gc_partial_conf"]
structure Config (β : Type) where
  limit : Nat
  isRef : β → Bool
  genStart : Nat
  refsStart : Nat

/-- Move one root in the collected generation. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_def"]
def gcMove {α β : Type} (conf : Config β) (state : GcState α β) :
    HeapAddress α → HeapAddress α × GcState α β
  | .data d => (.data d, state)
  | .pointer ptr d =>
    let ok := state.ok && decide (ptr < heapLength state.heap)
    if ptr < conf.genStart ∨ conf.refsStart ≤ ptr then
      (.pointer ptr d, { state with ok := ok })
    else
      match heapLookup ptr state.heap with
      | some (.dataElement xs len payload) =>
        let ok := ok && decide (len + 1 ≤ state.n) && !(conf.isRef payload)
        let n := state.n - (len + 1)
        let (heap, ok) := gcForwardPtr ptr state.heap state.a d ok
        (.pointer state.a d, { state with h2 := state.h2 ++ [.dataElement xs len payload], n := n, a := state.a + len + 1, heap := heap, ok := ok })
      | some (.forwardPointer newPtr _ _) => (.pointer newPtr d, state)
      | _ => (.pointer ptr d, { state with ok := false })

/-- Move each root in order. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_list_def"]
def gcMoveList {α β : Type} (conf : Config β) :
    GcState α β → List (HeapAddress α) → List (HeapAddress α) × GcState α β
  | state, [] => ([], state)
  | state, root :: roots =>
    let (root1, state1) := gcMove conf state root
    let (roots1, state2) := gcMoveList conf state1 roots
    (root1 :: roots1, state2)

/-- Update roots in reference elements until an invalid element is seen. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_ref_list_def"]
def gcMoveRefList {α β γ : Type} (conf : Config γ) :
    GcState α γ → List (HeapElement α β) → List (HeapElement α β) × GcState α γ
  | state, [] => ([], state)
  | state, .dataElement pointers len payload :: refs =>
    let (pointers1, state1) := gcMoveList conf state pointers
    let (refs1, state2) := gcMoveRefList conf state1 refs
    (.dataElement pointers1 len payload :: refs1, state2)
  | state, refs => (refs, { state with ok := false })

/-- Moving one root preserves the scanned left heap. -/
theorem gcMove_h1 {α β : Type} (conf : Config β) (state : GcState α β) (root : HeapAddress α) :
    (gcMove conf state root).2.h1 = state.h1 := by
  cases root with
  | data d => rfl
  | pointer ptr d =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [gcMove, outside]
    · cases h : heapLookup ptr state.heap with
      | none => simp [gcMove, outside, h]
      | some element => cases element <;> simp [gcMove, outside, h]

/-- Moving a root list preserves the scanned left heap. -/
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
/-- Scan copied data objects in the minor collection. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_data_def"]
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

open Classical in
/-- Collect one generation, starting with its roots and remembered references. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "partial_gc_def"]
noncomputable def partialGc {α β : Type} (conf : Config β)
    (input : List (HeapAddress α) × List (HeapElement α β)) : List (HeapAddress α) × GcState α β :=
  let (roots, heap) := input
  match heapSegment (conf.genStart, conf.refsStart) heap with
  | none => (roots, { emptyGcState with ok := false })
  | some (old, current, refs) =>
    let state := { emptyGcState with heap := heap, old := old, r2 := refs, a := conf.genStart, n := heapLength current }
    let (roots1, state1) := gcMoveList conf state roots
    let (refs1, state2) := gcMoveRefList conf state1 refs
    (roots1, gcMoveData conf { state2 with r1 := refs1, r2 := [] })

end Flapjack.Compiler.Backend.GenGcPartial
