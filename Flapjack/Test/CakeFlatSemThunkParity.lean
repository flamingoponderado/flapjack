import Flapjack.Compiler.Backend.Semantics.FlatSem.Thunk

/-! Matched original HOL observations from `cake_flat_sem_thunk_probe.out`. -/
namespace Flapjack.Test.CakeFlatSemThunkParity
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.FlatSem Flapjack.SemanticPrimitivesHOL

example : FlatSem.destThunk [.loc false 0] [.thunk .notEvaluated (.litv (.intLit 7))] =
    .isThunk .notEvaluated (.litv (.intLit 7)) := by rfl
example : FlatSem.destThunk [.loc true 0] [.thunk .notEvaluated (.litv (.intLit 7))] = .badRef := by rfl
example : FlatSem.destThunk [.loc false 1] [.thunk .notEvaluated (.litv (.intLit 7))] = .badRef := by rfl
example : FlatSem.destThunk [.loc true 0] [.refv (.litv (.intLit 7))] = .notThunk := by rfl
example : FlatSem.destThunk [.litv (.intLit 3)] [] = .notThunk := by rfl
example : FlatSem.updateThunk [.loc false 0] [.thunk .notEvaluated (.litv (.intLit 7))] [.litv (.intLit 9)] =
    some [.thunk .evaluated (.litv (.intLit 9))] := by rfl
example : FlatSem.updateThunk [.loc false 0] [.thunk .notEvaluated (.litv (.intLit 7))] [.loc false 0] = none := by rfl
end Flapjack.Test.CakeFlatSemThunkParity
