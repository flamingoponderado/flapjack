module

public import Flapjack.Compiler.Backend.GenGc

@[expose] public section

/-! Accumulator factoring for major-collector root movement. -/
namespace Flapjack.Compiler.Backend.GenGc

/-- Adding preexisting left and right objects commutes with a single move.
This stronger unconditional factoring is Flapjack-specific infrastructure. -/
theorem gcMove_accumulate {α β : Type} (conf : Config β) (state : GcState α β)
    (root : HeapAddress α) (left right : List (HeapElement α β)) :
    gcMove conf { state with h2 := left ++ state.h2, r4 := state.r4 ++ right } root =
      let (root1, state1) := gcMove conf state root
      (root1, { state1 with h2 := left ++ state1.h2, r4 := state1.r4 ++ right }) := by
  cases root with
  | data value => simp [gcMove]
  | pointer ptr value =>
    cases found : heapLookup ptr state.heap with
    | none => simp [gcMove, found]
    | some element =>
      cases element with
      | unused len => simp [gcMove, found]
      | forwardPointer dest old len => simp [gcMove, found]
      | dataElement xs len payload =>
        cases isRef : conf.isRef payload <;> simp [gcMove, found, isRef, List.append_assoc]

/-- The accumulator factoring extends to root lists. -/
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

end Flapjack.Compiler.Backend.GenGc
