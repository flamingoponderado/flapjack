import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyMemory

/-! Matched original HOL observations from `cake_flat_sem_apply_probe.out`. -/
namespace Flapjack.Test.CakeFlatSemMemoryParity
open Flapjack.Compiler.Backend.FlatSem

example {C F : Type} (s : State C F) :
    doAppMemory { s with refs := [.refv (.litv (.intLit 2))] } .opref [.litv (.intLit 7)] =
      some (some ({ s with refs := [.refv (.litv (.intLit 2)), .refv (.litv (.intLit 7))] }, .val (.loc true 1))) := by rfl
example {C F : Type} (s : State C F) :
    doAppMemory { s with refs := [.refv (.litv (.intLit 2))] } .opassign [.loc true 0, .litv (.intLit 7)] =
      some (some ({ s with refs := [.refv (.litv (.intLit 7))] }, .val unitValue)) := by rfl
example {C F : Type} (s : State C F) :
    doAppMemory { s with refs := [.w8array [1]] } .aw8sub [.loc true 0, .litv (.intLit 2)] =
      some (some ({ s with refs := [.w8array [1]] }, .err (.raise subscriptExnV))) := by rfl
example {C F : Type} (s : State C F) :
    doAppMemory { s with refs := [.w8array [1]] } .aw8subUnsafe [.loc true 0, .litv (.intLit 2)] = some none := by rfl
example {C F : Type} (s : State C F) :
    doAppMemory s .aalloc [.litv (.intLit (-1)), .litv (.intLit 7)] = some (some (s, .err (.raise subscriptExnV))) := by rfl
example {C F : Type} (s : State C F) :
    doAppMemory { s with refs := [.varray [.litv (.intLit 2)]] } .aupdate [.loc true 0, .litv (.intLit 0), .litv (.intLit 7)] =
      some (some ({ s with refs := [.varray [.litv (.intLit 7)]] }, .val unitValue)) := by rfl
example {C F : Type} (s : State C F) :
    doAppMemory { s with refs := [.w8array [1]] } .aupdate [.loc true 0, .litv (.intLit 0), .litv (.intLit 7)] = some none := by rfl
end Flapjack.Test.CakeFlatSemMemoryParity
