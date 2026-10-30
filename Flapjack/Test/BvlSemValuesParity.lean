import Flapjack.Compiler.Backend.Semantics.BvlSem.Int
import Flapjack.Compiler.Backend.Semantics.BvlSem.Equality
import Flapjack.Compiler.Backend.Semantics.BvlSem.Call
import Flapjack.Compiler.Backend.Semantics.BvlSem.Thunk
import Flapjack.Compiler.Backend.Semantics.BvlSem.Word
import Flapjack.Compiler.Backend.Semantics.BvlSem.Build
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateClock
import Flapjack.Compiler.Backend.Semantics.BvlSem.MemoryChoice
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

example {C F : Type} (s : State C F)
    (globals : s.globals = [some (.number 10), some (.number 20)]) :
    (applyGlobal (.global 0) [] s).map Prod.fst = some (.number 10) := by
  simp [applyGlobal, globals]

example {C F : Type} (s : State C F)
    (globals : s.globals = [some (.number 10), some (.number 20)]) :
    (applyGlobal (.global 0) [.number 0] s).map Prod.fst = some (.number 20) := by
  simp [applyGlobal, globals, Flapjack.Compiler.Backend.ClosToBvl.numAddedGlobals]

example {C F : Type} (s : State C F)
    (globals : s.globals = [some (.number 10), some (.number 20)]) :
    ((applyGlobal (.setGlobal 0) [.number 42] s).map (fun pair => pair.2.globals[0]?)).join =
      some (some (.number 42)) := by
  simp [applyGlobal, globals]

example {C F : Type} (s : State C F) :
    (applyBlock (.consExtend 3)
      [.block 9 [.number 5, .number 6], .number 1, .number 1, .number 2, .number 4] s).map Prod.fst =
      some (.block 3 [.number 4, .number 6]) := by simp [applyBlock]

example {C F : Type} (s : State C F)
    (refs : s.refs.lookup 0 = some (.valueArray [.number 7, .number 9])) :
    (applyBlock (.elemAt 1) [.refPtr true 0] s).map Prod.fst = some (.number 9) := by
  simp [applyBlock, refs]

example {C F : Type} (s : State C F) :
    (applyBlock (.build [.int 7, .con 3 [0]]) [] s).map Prod.fst =
      some (.block 3 [.number 7]) := by simp [applyBlock, doBuildConst, doBuild, doPart]

example {C F : Type} (s : State C F) :
    (applyNumeric (.intOp .add) [.number 7, .number 8] s).map Prod.fst = some (.number 15) := by
  simp [applyNumeric, doIntApp]

example {C F : Type} (s : State C F)
    (refs : s.refs.lookup 2 = some (.byteArray false [1, 2, 3])) :
    (applyMemory .lengthByte [.refPtr false 2] s).map Prod.fst = some (.number 3) := by
  simp [applyMemory, refs]

example {C F : Type} (s : State C F)
    (refs : s.refs.lookup 2 = some (.byteArray false [1, 2, 3])) :
    (applyMemory .derefByte [.refPtr true 2, .number 1] s).map Prod.fst = some (.number 2) := by
  simp [applyMemory, refs]

example {C F : Type} (s : State C F)
    (refs : s.refs.lookup 3 = some (.byteArray true [3, 4])) :
    ((applyMemory .updateByte [.refPtr false 3, .number 0, .number 255] s).map
      (fun pair => pair.2.refs.lookup 3)).join = some (.byteArray true [255, 4]) := by
  simp [applyMemory, refs, Flapjack.Compiler.Backend.ClosSem.intToByte,
    Flapjack.HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL]

example {C F : Type} (s : State C F)
    (refs : s.refs.lookup 2 = some (.byteArray false [1, 2, 3])) :
    (applyMemory (.boundsCheckByte true) [.refPtr true 2, .number 3] s).map Prod.fst =
      some (boolValue true) := by simp [applyMemory, refs]

example {C F : Type} (s : State C F) :
    (evaluate [.var 0] [.number 7] s).1 = .val [.number 7] := by
  simp [evaluate]

example {C F : Type} (s : State C F) :
    (evaluate [.let [.var 0, .var 1] (.var 1)] [.number 7, .number 9] s).1 =
      .val [.number 9] := by
  simp [evaluate, fixClock]

example {C F : Type} (s : State C F) :
    (evaluate [.handle (.raise (.var 0)) (.var 0)] [.number 7] s).1 =
      .val [.number 7] := by
  simp [evaluate, fixClock]

example {C F : Type} (s : State C F) :
    (evaluate [.op (.blockOp (.cons 4)) [.var 0, .var 1]] [.number 7, .number 9] s).1 =
      .val [.block 4 [.number 9, .number 7]] := by
  simp [evaluate, fixClock, doApp, applyBlock]

example {C F : Type} (s : State C F) (clock : s.clock = 0) :
    (evaluate [.tick (.var 0)] [.number 7] s).1 = .err (.abort .timeoutError) := by
  simp [evaluate, clock]

example {C F : Type} (s : State C F)
    (code : Flapjack.sptLookup 4 s.code = some (1, .var 0)) (clock : s.clock = 3) :
    (evaluate [.call 1 (some 4) [.var 0]] [.number 7] s).1 = .val [.number 7] ∧
    (evaluate [.call 1 (some 4) [.var 0]] [.number 7] s).2.clock = 1 := by
  simp [evaluate, fixClock, findCode, code, clock, decClock]

example : valueToBytes (listToValue [.number 1, .number 255]) = some [1, 255] := by
  rw [valueToBytes_eq_some, valueToList_listToValue]
  rfl

example : valueToWords (listToValue [.word64 1, .word64 2]) = some [1, 2] := by
  rw [valueToWords_eq_some, valueToList_listToValue]
  rfl

example (refs : Flapjack.HolFiniteMapExact Nat (Ref Value))
    (first : refs.lookup 2 = some (.byteArray true [1, 2]))
    (second : refs.lookup 3 = some (.byteArray true [3])) :
    byteArrayChunks refs (listToValue [.refPtr true 2, .refPtr true 3]) = some [[1, 2], [3]] := by
  simp [byteArrayChunks, valueToList_listToValue, byteArrays, first, second]

example (refs : Flapjack.HolFiniteMapExact Nat (Ref Value)) :
    byteArrayChunks refs (listToValue [.refPtr false 2]) = none := by
  simp [byteArrayChunks, valueToList_listToValue, byteArrays]

example (refs : Flapjack.HolFiniteMapExact Nat (Ref Value))
    (mutable : refs.lookup 2 = some (.byteArray false [1])) :
    byteArrayChunks refs (listToValue [.refPtr true 2]) = none := by
  simp [byteArrayChunks, valueToList_listToValue, byteArrays, mutable]

example {C F R : Type} (s : State C F) :
    doInstall (R := R) [] s = .err (.abort .typeError) := by simp [doInstall]

example {C F : Type} (s : State C F) (cfg nextCfg : C)
    (oracle : s.compileOracle 0 = (cfg, [(4, 1, .var 0)]))
    (nextOracle : (s.compileOracle 1).1 = nextCfg)
    (empty : Flapjack.sptLookup 4 s.code = none)
    (compiled : s.compile cfg [(4, 1, .var 0)] = some ([1], [2], nextCfg)) :
    doInstall (R := Value) [listToValue [.number 1], listToValue [.word64 2]] s =
      .val (.codePtr 4, { s with
        code := Flapjack.sptUnion s.code (Flapjack.sptFromAList [(4, 1, .var 0)])
        compileOracle := fun n => s.compileOracle (n + 1) }) := by
  have bytes : valueToBytes (listToValue [.number 1]) = some [1] := by
    rw [valueToBytes_eq_some, valueToList_listToValue]; rfl
  have words : valueToWords (listToValue [.word64 2]) = some [2] := by
    rw [valueToWords_eq_some, valueToList_listToValue]; rfl
  change valueToWords (listToValue [.word64 2#64]) = some [2#64] at words
  simp [doInstall, bytes, oracle, nextOracle, empty, compiled]
  rw [words]
  simp

end Flapjack.Test.BvlSemValuesParity
