import Flapjack.Compiler.Backend.CopyingGc

/-! Replays of `scripts/hol-probes/copying_gc_probe.out`. -/
namespace Flapjack.Test.CopyingGcParity
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.CopyingGc

example : gcMoveList (α := Nat) (β := Nat)
    ([.pointer 0 9, .pointer 0 10], [], 0, 2,
      [.dataElement [] 1 4], true, 2) =
    ([.pointer 0 9, .pointer 0 10], [.dataElement [] 1 4], 2, 0,
      [.forwardPointer 0 9 1], true) := by
  simp [gcMoveList, gcMove, heapLookup, gcForwardPtr, elLength]

example : fullGc (α := Nat) (β := Nat) ([.data 7], [.unused 1], 2) =
    ([.data 7], ([] : List (HeapElement Nat Nat)), 0, true) := by
  simp [fullGc, gcMoveList, gcMove, gcMoveLoop, heapLength, elLength]

example : fullGc (α := Nat) (β := Nat) ([.pointer 0 9], [.dataElement [.data 5] 1 4], 2) =
    ([.pointer 0 9], [.dataElement [.data 5] 1 4], 2, true) := by
  simp [fullGc, gcMoveList, gcMove, gcMoveLoop, heapLookup, gcForwardPtr, heapLength, elLength]

end Flapjack.Test.CopyingGcParity
