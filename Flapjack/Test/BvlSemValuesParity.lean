import Flapjack.Compiler.Backend.Semantics.BvlSem.Int
import Flapjack.Compiler.Backend.Semantics.BvlSem.Equality
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

private def equalBytes : Flapjack.HolFiniteMapExact Nat (Ref Unit) :=
  (Flapjack.HolFiniteMapExact.empty.update (1, .byteArray true [5, 6])).update
    (2, .byteArray true [5, 6])

private def mixedBytes : Flapjack.HolFiniteMapExact Nat (Ref Unit) :=
  (Flapjack.HolFiniteMapExact.empty.update (1, .byteArray true [5])).update
    (2, .byteArray false [5])

example : doEq equalBytes (.refPtr true 1) (.refPtr true 2) = .val true := by
  simp [doEq, equalBytes, Flapjack.HolFiniteMapExact.lookup_update, Flapjack.FUPDATE]

example : doEq mixedBytes (.refPtr true 1) (.refPtr true 2) = .typeError := by
  simp [doEq, mixedBytes, Flapjack.HolFiniteMapExact.lookup_update, Flapjack.FUPDATE]

example : doEq (Flapjack.HolFiniteMapExact.empty : Flapjack.HolFiniteMapExact Nat (Ref Unit))
    (.block 30 [.codePtr 3]) (.block 31 [.number 4]) = .val true := by
  simp [doEq, isClosure]

example : doEq (Flapjack.HolFiniteMapExact.empty : Flapjack.HolFiniteMapExact Nat (Ref Unit))
    (.codePtr 1) (.codePtr 1) = .typeError := by simp [doEq]

example : doEqList (Flapjack.HolFiniteMapExact.empty : Flapjack.HolFiniteMapExact Nat (Ref Unit))
    [.number 1, .codePtr 0] [.number 2, .codePtr 0] = .val false := by simp [doEqList, doEq]

end Flapjack.Test.BvlSemValuesParity
