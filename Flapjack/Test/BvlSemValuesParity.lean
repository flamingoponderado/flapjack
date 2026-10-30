import Flapjack.Compiler.Backend.Semantics.BvlSem.Int
import Flapjack.Compiler.Backend.Semantics.BvlSem.Equality
import Flapjack.Compiler.Backend.Semantics.BvlSem.Call
import Flapjack.Compiler.Backend.Semantics.BvlSem.Thunk
import Flapjack.Compiler.Backend.Semantics.BvlSem.Word
import Flapjack.Compiler.Backend.Semantics.BvlSem.Build
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

example : doWordApp (.wordOpw .w8 .add) [.number 255, .number 2] = some (.number 1) := by
  rfl
example : doWordApp (.wordOpw .w8 .add) [.number 256, .number 2] = none := by rfl
example : doWordApp (.wordFromWord true) [.word64 511] = some (.number 255) := by rfl
example : doWordApp .wordFromInt [.number (-1)] = some (.word64 (-1)) := by rfl

private def emptyRefs : Flapjack.HolFiniteMapExact Nat (Ref Value) := Flapjack.HolFiniteMapExact.empty

example : (doBuildConst [] emptyRefs).1 = .number 0 := by simp [doBuildConst, doBuild]

example : (doBuildConst [.int 7, .int 9, .con 20 [0, 1]] emptyRefs).1 =
    .block 20 [.number 7, .number 9] := by simp [doBuildConst, doBuild, doPart]

example : (doBuildConst [.str (Flapjack.Basis.Pure.MlString.ofString "ab")] emptyRefs).1 =
    .refPtr true 0 := by
  have fresh : leastUnusedRef emptyRefs = 0 := leastUnusedRef_eq_zero emptyRefs rfl
  simp [doBuildConst, doBuild, doPart, fresh]

example : (doBuildConst [.str (Flapjack.Basis.Pure.MlString.ofString "ab")] emptyRefs).2.lookup 0 =
    some (.byteArray true [97, 98]) := by
  have fresh : leastUnusedRef emptyRefs = 0 := leastUnusedRef_eq_zero emptyRefs rfl
  simp [doBuildConst, doBuild, doPart, fresh, Flapjack.HolFiniteMapExact.lookup_updateEq,
    Flapjack.FUPDATE_HOL, Flapjack.Basis.Pure.MlString.ofString,
    Flapjack.Basis.Pure.MlString.MlString.explode]

private def occupiedZero : Flapjack.HolFiniteMapExact Nat (Ref Value) :=
  emptyRefs.updateEq (0, .valueArray [])

private theorem occupiedZero_fresh : leastUnusedRef occupiedZero = 1 := by
  apply leastUnusedRef_eq
  · simp [occupiedZero, emptyRefs, Flapjack.HolFiniteMapExact.lookup_updateEq,
      Flapjack.FUPDATE_HOL, Flapjack.HolFiniteMapExact.empty]
  · intro n hn
    have : n = 0 := by omega
    subst n
    simp [occupiedZero, emptyRefs, Flapjack.HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL]

example : (doBuildConst [.str (Flapjack.Basis.Pure.MlString.ofString "x")] occupiedZero).1 =
    .refPtr true 1 := by simp [doBuildConst, doBuild, doPart, occupiedZero_fresh]

example : (doBuildConst [.str (Flapjack.Basis.Pure.MlString.ofString "x")] occupiedZero).2.lookup 1 =
    some (.byteArray true [120]) := by
  simp [doBuildConst, doBuild, doPart, occupiedZero_fresh, Flapjack.HolFiniteMapExact.lookup_updateEq,
    Flapjack.FUPDATE_HOL, Flapjack.Basis.Pure.MlString.ofString,
    Flapjack.Basis.Pure.MlString.MlString.explode]

end Flapjack.Test.BvlSemValuesParity
