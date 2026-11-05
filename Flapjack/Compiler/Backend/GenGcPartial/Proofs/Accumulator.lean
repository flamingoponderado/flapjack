import Flapjack.Compiler.Backend.GenGcPartial

/-! Accumulator factoring for partial generational collection. -/
namespace Flapjack.Compiler.Backend.GenGcPartial

/-- Flapjack infrastructure: root moves commute with arbitrary updates to
the two remembered-reference fields. -/
theorem gcMove_withReferenceFields {α β : Type} (conf : Config β) (state : GcState α β)
    (root : HeapAddress α) (refs1 refs2 : List (HeapElement α β)) :
    gcMove conf { state with r1 := refs1, r2 := refs2 } root =
      let (root1, state1) := gcMove conf state root
      (root1, { state1 with r1 := refs1, r2 := refs2 }) := by
  cases root with
  | data value => simp [gcMove]
  | pointer ptr value =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [gcMove, outside]
    · cases found : heapLookup ptr state.heap with
      | none => simp [gcMove, outside, found]
      | some element => cases element <;> simp [gcMove, outside, found]

/-- Flapjack infrastructure: root-list moves commute with remembered-reference
updates. -/
theorem gcMoveList_withReferenceFields {α β : Type} (conf : Config β)
    (state : GcState α β) (roots : List (HeapAddress α))
    (refs1 refs2 : List (HeapElement α β)) :
    gcMoveList conf { state with r1 := refs1, r2 := refs2 } roots =
      let (roots1, state1) := gcMoveList conf state roots
      (roots1, { state1 with r1 := refs1, r2 := refs2 }) := by
  induction roots generalizing state with
  | nil => rfl
  | cons root roots ih =>
    simp only [gcMoveList, gcMove_withReferenceFields]
    generalize h : gcMove conf state root = result
    obtain ⟨root1, state1⟩ := result
    simp only
    rw [ih state1]

/-- Flapjack infrastructure: copied-data scanning commutes with arbitrary
updates to the remembered-reference fields. -/
theorem gcMoveData_withReferenceFields {α β : Type} (conf : Config β) (state : GcState α β) :
    ∀ refs1 refs2 : List (HeapElement α β),
      gcMoveData conf { state with r1 := refs1, r2 := refs2 } =
        { gcMoveData conf state with r1 := refs1, r2 := refs2 } := by
  classical
  induction state using gcMoveData.induct conf with
  | case1 state empty =>
    intro refs1 refs2
    rw [gcMoveData, gcMoveData]
    simp [empty]
  | case2 state head tail heap over =>
    intro refs1 refs2
    rw [gcMoveData, gcMoveData]
    simp [heap, over]
  | case3 state tail roots len payload roots1 middle move heap bounded flag ih =>
    intro refs1 refs2
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n status origHeap heap0 =>
      simp only at heap
      subst h2
      have moved := gcMoveList_withReferenceFields conf
        (GcState.mk old h1 (.dataElement roots len payload :: tail) r4 r3 r2 r1 a n status origHeap heap0)
        roots refs1 refs2
      rw [move] at moved
      rw [gcMoveData, gcMoveData]
      simp only [bounded, ↓reduceIte, move, moved]
      dsimp only [flag] at ih
      exact ih refs1 refs2
  | case4 state head tail heap bounded notData =>
    intro refs1 refs2
    cases head with
    | unused len => rw [gcMoveData, gcMoveData]; simp [heap, bounded]
    | forwardPointer ptr value len => rw [gcMoveData, gcMoveData]; simp [heap, bounded]
    | dataElement roots len payload => exact False.elim (notData roots len payload rfl)

/-- Root movement commutes with installing scanned references and clearing the
input reference queue. The local HOL proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_with_refs'"]
theorem gcMove_withRefsCleared {α β : Type} (conf : Config β) (state : GcState α β)
    (root : HeapAddress α) (refs : List (HeapElement α β)) :
    gcMove conf { state with r2 := [], r1 := refs } root =
      let (root1, state1) := gcMove conf state root
      (root1, { state1 with r2 := [], r1 := refs }) :=
  gcMove_withReferenceFields conf state root refs []

/-- Root-list movement commutes with the reference-field update. The local HOL
proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_list_with_refs'"]
theorem gcMoveList_withRefsCleared {α β : Type} (conf : Config β) (state : GcState α β)
    (roots : List (HeapAddress α)) (refs : List (HeapElement α β)) :
    gcMoveList conf { state with r2 := [], r1 := refs } roots =
      let (roots1, state1) := gcMoveList conf state roots
      (roots1, { state1 with r2 := [], r1 := refs }) :=
  gcMoveList_withReferenceFields conf state roots refs []

/-- Copied-data scanning commutes with the reference-field update. The local
HOL proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_data_with_refs'"]
theorem gcMoveData_withRefsCleared {α β : Type} (conf : Config β) (state : GcState α β)
    (refs : List (HeapElement α β)) :
    gcMoveData conf { state with r2 := [], r1 := refs } =
      { gcMoveData conf state with r2 := [], r1 := refs } :=
  gcMoveData_withReferenceFields conf state refs []

/-- Adding preexisting accumulators commutes with a partial root move. This
stronger unconditional equality is local Flapjack proof infrastructure. -/
theorem gcMove_accumulate {α β : Type} (conf : Config β) (state : GcState α β)
    (root : HeapAddress α) (left right : List (HeapElement α β)) :
    gcMove conf { state with h2 := left ++ state.h2, r4 := state.r4 ++ right } root =
      let (root1, state1) := gcMove conf state root
      (root1, { state1 with h2 := left ++ state1.h2, r4 := state1.r4 ++ right }) := by
  cases root with
  | data value => simp [gcMove]
  | pointer ptr value =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [gcMove, outside]
    · cases found : heapLookup ptr state.heap with
      | none => simp [gcMove, outside, found]
      | some element =>
        cases element with
        | unused len => simp [gcMove, outside, found]
        | forwardPointer dest old len => simp [gcMove, outside, found]
        | dataElement xs len payload => simp [gcMove, outside, found, List.append_assoc]

/-- The same factoring commutes with a whole root traversal. -/
theorem gcMoveList_accumulate {α β : Type} (conf : Config β) (state : GcState α β)
    (roots : List (HeapAddress α)) (left right : List (HeapElement α β)) :
    gcMoveList conf { state with h2 := left ++ state.h2, r4 := state.r4 ++ right } roots =
      let (roots1, state1) := gcMoveList conf state roots
      (roots1, { state1 with h2 := left ++ state1.h2, r4 := state1.r4 ++ right }) := by
  induction roots generalizing state with
  | nil => rfl
  | cons root roots ih =>
    simp only [gcMoveList, gcMove_accumulate]
    generalize h : gcMove conf state root = result
    rcases result with ⟨root1, state1⟩
    simp only
    rw [ih state1]

/-- Adding preexisting accumulators commutes with scanning a reference list.
This unconditional equality is local Flapjack proof infrastructure. -/
theorem gcMoveRefList_accumulate {α β γ : Type} (conf : Config γ) (state : GcState α γ)
    (refs : List (HeapElement α β)) (left right : List (HeapElement α γ)) :
    gcMoveRefList conf { state with h2 := left ++ state.h2, r4 := state.r4 ++ right } refs =
      let (refs1, state1) := gcMoveRefList conf state refs
      (refs1, { state1 with h2 := left ++ state1.h2, r4 := state1.r4 ++ right }) := by
  induction refs generalizing state with
  | nil => rfl
  | cons head refs ih =>
    cases head with
    | unused len => rfl
    | forwardPointer ptr value len => rfl
    | dataElement roots len payload =>
      simp only [gcMoveRefList, gcMoveList_accumulate]
      generalize run : gcMoveList conf state roots = result
      obtain ⟨roots1, state1⟩ := result
      simp only
      rw [ih state1]

/-- Partial root moves leave the reference accumulator unchanged. -/
theorem gcMove_r4 {α β : Type} (conf : Config β) (state : GcState α β) (root : HeapAddress α) :
    (gcMove conf state root).2.r4 = state.r4 := by
  cases root with
  | data value => rfl
  | pointer ptr value =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [gcMove, outside]
    · cases found : heapLookup ptr state.heap with
      | none => simp [gcMove, outside, found]
      | some element => cases element <;> simp [gcMove, outside, found]

/-- Partial root traversals leave the reference accumulator unchanged. -/
theorem gcMoveList_r4 {α β : Type} (conf : Config β) (state : GcState α β)
    (roots : List (HeapAddress α)) : (gcMoveList conf state roots).2.r4 = state.r4 := by
  induction roots generalizing state with
  | nil => rfl
  | cons root roots ih =>
    simp only [gcMoveList]
    generalize run : gcMove conf state root = result
    obtain ⟨root1, state1⟩ := result
    have head := gcMove_r4 conf state root
    rw [run] at head
    exact (ih state1).trans head

end Flapjack.Compiler.Backend.GenGcPartial
