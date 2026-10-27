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
end Flapjack.Test.CakeFlatSemApplyCompleteParity
