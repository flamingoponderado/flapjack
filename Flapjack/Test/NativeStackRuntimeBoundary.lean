import Flapjack.Compiler.Backend.StackToLab.Production

/-! Kernel fixtures for the executed native compiler boundary; not HOL theorem ports. -/
namespace Flapjack.Test.NativeStackRuntimeBoundary
open Flapjack Flapjack.Compiler.Backend.StackToLab

example : (Production.removedSection? (width := 64) true (BitVec.ofInt 64 (-2048), 2047)
    24 (7, .stackFree 511)).isSome = true := by decide +kernel

example : (Production.removedSection? (width := 64) false (BitVec.ofInt 64 (-2048), 2047)
    24 (7, .stackAlloc 256)).isSome = true := by decide +kernel

example : (Production.removedSection? (width := 64) true (0, 0)
    24 (7, .stackLoad 5 256)).isSome = true := by decide +kernel

-- Honest residual-operation rejection after native removal; no legacy fallback.
example : (Production.removedSection? (width := 64) true (0, 0)
    24 (7, .alloc 8)).isSome = false := by decide +kernel

#print axioms Production.removedSection_recover
end Flapjack.Test.NativeStackRuntimeBoundary
