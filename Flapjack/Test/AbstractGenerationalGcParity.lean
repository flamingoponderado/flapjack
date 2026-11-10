module

public import Flapjack.Compiler.Backend.GenGc
public import Flapjack.Compiler.Backend.GenGcPartial
public import Flapjack.Compiler.Backend.GcCombined.Collector

@[expose] public section

/-! HOL observations captured in `data_to_word_gc_stack_probe.out`. -/
namespace Flapjack.Test.AbstractGenerationalGcParity
open Flapjack.Compiler.Backend

private def initial : GcState Nat Nat :=
  { emptyGcState with heap := [.dataElement [] 0 42], n := 3 }

-- Original major collector places classified references at the heap end.
example :
    let (root, state) := GenGc.gcMove ⟨3, fun n => n == 42⟩ initial (.pointer 0 7)
    (root, state.a, state.n, state.ok, state.r4, state.h2) =
      (.pointer 2 7, 0, 2, true, [.dataElement [] 0 42], []) := by rfl

-- Ordinary data is copied at the allocation pointer instead.
example :
    let (root, state) := GenGc.gcMove ⟨3, fun _ => false⟩ initial (.pointer 0 7)
    (root, state.a, state.n, state.ok, state.r4, state.h2) =
      (.pointer 0 7, 1, 2, true, [], [.dataElement [] 0 42]) := by rfl

-- An already forwarded minor-collection pointer retains the incoming status.
example :
    let state : GcState Nat Nat := { emptyGcState with heap := [.forwardPointer 2 9 0], n := 3, ok := false }
    let (root, state) := GenGcPartial.gcMove ⟨3, fun _ => false, 0, 3⟩ state (.pointer 0 7)
    (root, state.a, state.n, state.ok) = (.pointer 2 7, 0, 3, false) := by rfl

example :
    GcCombined.gcCombined (α := Nat) (⟨0, fun _ : Nat => false⟩) (.generational [0])
      ([], [], .genState 0 [0], 0, false) = ([], [], 0, 0, .genState 0 [0], true) := by
  simp [GcCombined.gcCombined, GenGc.genGc, GenGc.gcMoveList, GenGc.gcMoveLoop,
    emptyGcState, heapLength, heapExpand]

example :
    GcCombined.gcCombined (α := Nat) (⟨0, fun _ : Nat => false⟩) (.generational [0])
      ([], [], .genState 0 [0], 0, true) = ([], [], 0, 0, .genState 0 [0], true) := by
  simp [GcCombined.gcCombined, GcCombined.makePartialConf, GenGcPartial.partialGc,
    GenGcPartial.gcMoveList, GenGcPartial.gcMoveRefList, GenGcPartial.gcMoveData,
    heapSegment, heapSplit, emptyGcState, heapLength, heapExpand, Flapjack.holHd]

end Flapjack.Test.AbstractGenerationalGcParity
