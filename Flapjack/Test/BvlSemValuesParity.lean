import Flapjack.Compiler.Backend.Semantics.BvlSem.Int
import Flapjack.Compiler.Backend.Semantics.BvlSem.Equality
import Flapjack.Compiler.Backend.Semantics.BvlSem.Call
import Flapjack.Compiler.Backend.Semantics.BvlSem.Thunk
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

private def sampleCode : Flapjack.Spt (Nat × Flapjack.Compiler.Backend.Bvl.Exp) :=
  Flapjack.sptInsert 4 (2, .var 3) .ln

example : findCode (some 4) [.number 10, .number 20] sampleCode =
    some ([.number 10, .number 20], .var 3) := by
  simp [findCode, sampleCode, Flapjack.sptLookup_sptInsert_same]

example : findCode none [.number 10, .number 20, .codePtr 4] sampleCode =
    some ([.number 10, .number 20], .var 3) := by
  simp [findCode, sampleCode, Flapjack.holLast, Flapjack.sptLookup_sptInsert_same]

example : findCode none [.number 10, .codePtr 4] sampleCode = none := by
  simp [findCode, sampleCode, Flapjack.holLast, Flapjack.sptLookup_sptInsert_same]

example : findCode none [.number 4] sampleCode = none := by simp [findCode, Flapjack.holLast]
example : findCode none [] (Flapjack.Spt.ln : Flapjack.Spt (Nat × Unit)) = none := by simp [findCode]

private def sampleThunk : Flapjack.HolFiniteMapExact Nat (Ref Value) :=
  Flapjack.HolFiniteMapExact.empty.update (1, .thunk .evaluated (.number 7))

example : destThunk (.refPtr false 1) sampleThunk = .isThunk .evaluated (.number 7) := by
  simp [destThunk, sampleThunk, Flapjack.HolFiniteMapExact.lookup_update, Flapjack.FUPDATE]
example : destThunk (.refPtr true 1) sampleThunk = .badRef := by
  simp [destThunk, sampleThunk, Flapjack.HolFiniteMapExact.lookup_update, Flapjack.FUPDATE]
example : destThunk (.refPtr false 1) Flapjack.HolFiniteMapExact.empty = .badRef := by
  simp [destThunk, Flapjack.HolFiniteMapExact.empty]
example : destThunk (.number 1) Flapjack.HolFiniteMapExact.empty = .notThunk := by simp [destThunk]

end Flapjack.Test.BvlSemValuesParity
