import Flapjack.Compiler.Backend.Semantics.BvlSem.Int
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ClosureArguments

/-! Kernel replay of representative original BVL semantic observations. -/
namespace Flapjack.Test.BvlSemValuesParity
open Flapjack.Compiler.Backend.BvlSem

example : doIntApp .div [.number (-10), .number 3] = some (.number (-4)) := by rfl
example : doIntApp .mod [.number (-10), .number 3] = some (.number 2) := by rfl
example : doIntApp .div [.number 10, .number (-3)] = some (.number (-4)) := by rfl
example : doIntApp .mod [.number 10, .number (-3)] = some (.number (-2)) := by rfl
example : doIntApp .div [.number 1, .number 0] = none := by rfl
example : valueToList (listToValue [.number 1, .number 2]) = some [.number 1, .number 2] := by
  simp [valueToList, listToValue, Flapjack.Compiler.Backend.BackendCommon.nilTag,
    Flapjack.Compiler.Backend.BackendCommon.consTag]
example : valueToList (.block 1 []) = none := by
  simp [valueToList, Flapjack.Compiler.Backend.BackendCommon.nilTag]

end Flapjack.Test.BvlSemValuesParity
