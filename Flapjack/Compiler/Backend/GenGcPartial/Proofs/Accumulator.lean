import Flapjack.Compiler.Backend.GenGcPartial

/-! Accumulator factoring for partial generational collection. -/
namespace Flapjack.Compiler.Backend.GenGcPartial

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
