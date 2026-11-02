import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply

/-! Matched observations from `cake_flat_sem_apply_probe.out`, through the
assembled dispatcher. -/
namespace Flapjack.Test.CakeFlatSemApplyCompleteParity
open Flapjack.Compiler.Backend.FlatSem
open Flapjack.Basis.Pure.MlString

example {C F : Type} (s : State C F) :
    doApp s (.src .strlen) [.litv (.strLit (ofString "abc"))] =
      some (s, .val (.litv (.intLit 3))) := by rfl
example {C F : Type} (s : State C F) :
    doApp s (.src .strsub) [.litv (.strLit (ofString "abc")), .litv (.intLit (-1))] =
      some (s, .err (.raise subscriptExnV)) := by rfl
example {C F : Type} (s : State C F) :
    doApp s (.src .vsub) [.vectorv [.litv (.intLit 4)], .litv (.intLit 0)] =
      some (s, .val (.litv (.intLit 4))) := by rfl
example {C F : Type} (s : State C F) :
    doApp s (.src .vsubUnsafe) [.vectorv [.litv (.intLit 4)], .litv (.intLit 1)] = none := by rfl
example {C F : Type} (s : State C F) :
    doApp s (.src .copyStrStr) [.litv (.strLit (ofString "abcd")), .litv (.intLit 1), .litv (.intLit 2)] =
      some (s, .val (.litv (.strLit (ofString "bc")))) := by rfl
example {C F : Type} (s : State C F) :
    doApp s (.src .copyStrStr) [.litv (.strLit (ofString "abcd")), .litv (.intLit 3), .litv (.intLit 2)] =
      some (s, .err (.raise subscriptExnV)) := by rfl
example {C F : Type} (s : State C F) :
    doApp { s with refs := [] } (.src (.thunkOp (.allocThunk .notEvaluated))) [.litv (.intLit 5)] =
      some ({ s with refs := [.thunk .notEvaluated (.litv (.intLit 5))] }, .val (.loc false 0)) := by rfl
example {C F : Type} (s : State C F) :
    doApp s (.src (.shift .w8 .lsl 2)) [.litv (.word8 7)] = some (s, .val (.litv (.word8 28))) := by rfl
example {C F : Type} (s : State C F) :
    doApp s (.globalVarAlloc 2) [] = some ({ s with globals := s.globals ++ [none, none] }, .val unitValue) := by rfl
example {C F : Type} (s : State C F) :
    doApp { s with refs := [] } (.src .opref) [.litv (.intLit 7)] =
      some ({ s with refs := [.refv (.litv (.intLit 7))] }, .val (.loc true 0)) := by rfl
example {C F : Type} (s : State C F) :
    doApp { s with refs := [.w8array [1, 2, 3, 4]] } (.src .copyAw8Aw8)
      [.loc true 0, .litv (.intLit 0), .litv (.intLit 3), .loc true 0, .litv (.intLit 1)] =
      some ({ s with refs := [.w8array [1, 1, 2, 3]] }, .val unitValue) := by rfl
example {C F : Type} (s : State C F) :
    doApp { s with refs := [.w8array [0, 0, 0]] } (.src .copyStrAw8)
      [.litv (.strLit (ofString "ABC")), .litv (.intLit 1), .litv (.intLit 2),
        .loc true 0, .litv (.intLit 1)] =
      some ({ s with refs := [.w8array [0, 66, 67]] }, .val unitValue) := by rfl
example {C F : Type} (s : State C F) :
    doApp { s with refs := [.w8array [0, 65, 255]] } (.src .copyAw8Str)
      [.loc true 0, .litv (.intLit 1), .litv (.intLit 2)] =
      some ({ s with refs := [.w8array [0, 65, 255]] }, .val (.litv (.strLit (.implode [65, 255])))) := by rfl
example {C F : Type} (s : State C F) :
    doApp { s with refs := [.w8array [0]] } (.src .copyStrAw8)
      [.litv (.strLit (ofString "A")), .litv (.intLit 0), .litv (.intLit 1),
        .loc true 0, .litv (.intLit (-1))] =
      some ({ s with refs := [.w8array [0]] }, .err (.raise subscriptExnV)) := by rfl
example {C F : Type} (s : State C F) :
    doApp { s with refs := [.refv (.litv (.intLit 1))] } (.src .copyAw8Str)
      [.loc true 0, .litv (.intLit 0), .litv (.intLit 1)] = none := by rfl
example {C F : Type} (s : State C F) :
    doApp { s with refs := [.w8array [3, 5, 7]] } (.src .xorAw8StrUnsafe)
      [.loc true 0, .litv (.strLit (ofString "AB"))] =
      some ({ s with refs := [.w8array [66, 71, 7]] }, .val unitValue) := by rfl
example {C F : Type} (s : State C F) :
    doApp { s with refs := [.w8array [3]] } (.src .xorAw8StrUnsafe)
      [.loc true 0, .litv (.strLit (ofString "AB"))] = none := by rfl
example {C F : Type} (s : State C F) :
    doApp s (.src .implode) [listToValue [.litv (.char 65), .litv (.char 66)]] =
      some (s, .val (.litv (.strLit (.implode [65, 66])))) := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, valueToCharList, listToValue,
    Flapjack.Compiler.Backend.BackendCommon.nilTag, Flapjack.Compiler.Backend.BackendCommon.consTag, listId]
example {C F : Type} (s : State C F) :
    doApp s (.src .explode) [.litv (.strLit (ofString "AB"))] =
      some (s, .val (listToValue [.litv (.char 65), .litv (.char 66)])) := by rfl
example {C F : Type} (s : State C F) :
    doApp s (.src .strcat) [listToValue [.litv (.strLit (ofString "A")), .litv (.intLit 1)]] = none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, valueToList, listToValue, valuesToString,
    Flapjack.Compiler.Backend.BackendCommon.nilTag, Flapjack.Compiler.Backend.BackendCommon.consTag, listId]
example {C F : Type} (s : State C F) :
    doApp s (.src .vfromList) [listToValue [.litv (.intLit 1), .litv (.intLit 2)]] =
      some (s, .val (.vectorv [.litv (.intLit 1), .litv (.intLit 2)])) := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, valueToList, listToValue,
    Flapjack.Compiler.Backend.BackendCommon.nilTag, Flapjack.Compiler.Backend.BackendCommon.consTag, listId]
example {C F : Type} (s : State C F) :
    doApp s (.src .vlength) [.vectorv [.litv (.intLit 1), .litv (.intLit 2)]] =
      some (s, .val (.litv (.intLit 2))) := by rfl
example {C F : Type} (s : State C F) :
    doApp s (.src .listAppend) [listToValue [.litv (.intLit 1)], listToValue [.litv (.intLit 2)]] =
      some (s, .val (listToValue [.litv (.intLit 1), .litv (.intLit 2)])) := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, valueToList, listToValue,
    Flapjack.Compiler.Backend.BackendCommon.nilTag, Flapjack.Compiler.Backend.BackendCommon.consTag, listId]
example {C F : Type} (s : State C F) :
    doApp s (.src .configGC) [.litv (.intLit (-3)), .litv (.intLit 7)] = some (s, .val unitValue) := by rfl
example {C F : Type} (s : State C F) :
    doApp { s with refs := [.thunk .notEvaluated (.litv (.intLit 1))] }
      (.src (.thunkOp (.updateThunk .evaluated))) [.loc false 0, .litv (.intLit 2)] =
      some ({ s with refs := [.thunk .evaluated (.litv (.intLit 2))] }, .val unitValue) := by rfl
example {C F : Type} (s : State C F) :
    doApp { s with refs := [.thunk .notEvaluated (.litv (.intLit 1))] }
      (.src (.thunkOp (.updateThunk .evaluated))) [.loc true 0, .litv (.intLit 2)] = none := by rfl
example {C F : Type} (s : State C F) :
    doApp { s with refs := [.w8array [1, 2]] } (.src (.ffi (ofString "")))
      [.litv (.strLit (ofString "x")), .loc true 0] =
      some ({ s with refs := [.w8array [1, 2]] }, .val unitValue) := by rfl
example {C F : Type} (s : State C F) :
    doApp { s with refs := [.refv (.litv (.intLit 1))] } (.src (.ffi (ofString "x")))
      [.litv (.strLit (ofString "")), .loc true 0] = none := by rfl
end Flapjack.Test.CakeFlatSemApplyCompleteParity
