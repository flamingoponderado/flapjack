import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyFlat

/-! Matched original HOL observations from `cake_flat_sem_apply_probe.out`. -/
namespace Flapjack.Test.CakeFlatSemApplyParity
open Flapjack.Compiler.Backend.FlatSem

example {C F : Type} (s : State C F) :
    doAppFlat { s with globals := [] } (.globalVarAlloc 2) [] =
      some (some ({ s with globals := [none, none] }, .val unitValue)) := by rfl
example {C F : Type} (s : State C F) :
    doAppFlat { s with globals := [none] } (.globalVarInit 0) [.litv (.intLit 7)] =
      some (some ({ s with globals := [some (.litv (.intLit 7))] }, .val unitValue)) := by rfl
example {C F : Type} (s : State C F) :
    doAppFlat { s with globals := [some (.litv (.intLit 3))] } (.globalVarInit 0) [.litv (.intLit 7)] = some none := by rfl
example {C F : Type} (s : State C F) :
    doAppFlat { s with globals := [some (.litv (.intLit 7))] } (.globalVarLookup 0) [] =
      some (some ({ s with globals := [some (.litv (.intLit 7))] }, .val (.litv (.intLit 7)))) := by rfl
example {C F : Type} (s : State C F) : doAppFlat { s with globals := [none] } (.globalVarLookup 0) [] = some none := by rfl
example {C F : Type} (s : State C F) :
    doAppFlat s (.tagLenEq 2 1) [.conv (some (2, none)) [.litv (.intLit 7)]] = some (some (s, .val (boolValue true))) := by rfl
example {C F : Type} (s : State C F) :
    doAppFlat s (.tagLenEq 3 1) [.conv (some (2, none)) [.litv (.intLit 7)]] = some (some (s, .val (boolValue false))) := by rfl
example {C F : Type} (s : State C F) :
    doAppFlat s (.lenEq 1) [.conv none [.litv (.intLit 7)]] = some (some (s, .val (boolValue true))) := by rfl
example {C F : Type} (s : State C F) :
    doAppFlat s (.el 0) [.conv none [.litv (.intLit 7)]] = some (some (s, .val (.litv (.intLit 7)))) := by rfl
example {C F : Type} (s : State C F) :
    doAppFlat { s with refs := [.refv (.litv (.intLit 7))] } (.el 0) [.loc true 0] =
      some (some ({ s with refs := [.refv (.litv (.intLit 7))] }, .val (.litv (.intLit 7)))) := by rfl
example {C F : Type} (s : State C F) :
    doAppFlat { s with refs := [.refv (.litv (.intLit 7))] } (.el 1) [.loc true 0] = some none := by rfl
example {C F : Type} (s : State C F) : doAppFlat s .id [.litv (.intLit 7)] = some (some (s, .val (.litv (.intLit 7)))) := by rfl
end Flapjack.Test.CakeFlatSemApplyParity
