import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact

/-! Unbounded flat evaluation compared with the original HOL observations in
`cake_flat_sem_evaluate_probe.out`. -/
namespace Flapjack.Test.CakeFlatSemEvaluateExactParity
open Flapjack.Compiler.Backend.FlatSem Flapjack.Compiler.Backend.FlatLang
open Flapjack.Basis.Pure.MlString

private def env : Environment Value := ⟨[]⟩
private def x := ofString "x"
private def call : Flapjack.Compiler.Backend.FlatLang.Exp := .app .none (.src .opapp)
  [.fn (ofString "unused") x (.varLocal .none x), .lit .none (.intLit 7)]

example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 4 } [.lit .none (.intLit 3)] =
      ({ s with clock := 4 }, .val [.litv (.intLit 3)]) := by simp [evaluate]
example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 4 } [.varLocal .none x] =
      ({ s with clock := 4 }, .err (.abort .typeError)) := by simp [evaluate, env, x]
example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 4 } [call] =
      ({ s with clock := 3 }, .val [.litv (.intLit 7)]) := by
  simp [call, evaluate, env, x, fixClock, doOpApp, decClock]
example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 0 } [call] =
      ({ s with clock := 0 }, .err (.abort .timeoutError)) := by
  simp [call, evaluate, env, x, fixClock, doOpApp]
example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 4, refs := [] }
      [.con .none none [.app .none (.src .opref) [.lit .none (.intLit 1)],
        .app .none (.src .opref) [.lit .none (.intLit 2)]]] =
      ({ s with clock := 4, refs := [.refv (.litv (.intLit 2)), .refv (.litv (.intLit 1))] },
        .val [.conv none [.loc true 1, .loc true 0]]) := by
  simp [evaluate, env, fixClock, doApp, doAppNumeric, doAppMemory, Flapjack.SemanticPrimitivesHOL.storeAlloc]
example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 4 } [.mat .none (.lit .none (.intLit 1)) []] =
      ({ s with clock := 4 }, .err (.raise bindExnV)) := by
  simp [evaluate, env, fixClock, selectRow, pmatchRows]
example {C F : Type} (s : State C F) :
    evaluate ⟨[(ofString "t", .loc false 0)]⟩
      { s with clock := 4, refs := [.thunk .notEvaluated (.closure env (ofString "u") (.lit .none (.intLit 5)))] }
      [.app .none (.src (.thunkOp .forceThunk)) [.varLocal .none (ofString "t")]] =
      ({ s with clock := 3, refs := [.thunk .evaluated (.litv (.intLit 5))] }, .val [.litv (.intLit 5)]) := by
  simp [evaluate, env, fixClock, appUnit, destThunk, doOpApp, decClock, updateThunk,
    Flapjack.SemanticPrimitivesHOL.storeLookup, Flapjack.SemanticPrimitivesHOL.storeAssign,
    Flapjack.SemanticPrimitivesHOL.storeValueSameType]
example {C F : Type} (s : State C F) :
    evaluateDecs { s with clock := 4 } [.con .none none []] = ({ s with clock := 4 }, none) := by
  simp [evaluateDecs, evaluate, fixClock]
example {C F : Type} (s : State C F) :
    evaluateDecs { s with clock := 4 } [.lit .none (.intLit 1)] =
      ({ s with clock := 4 }, some (.abort .typeError)) := by
  simp [evaluateDecs, evaluate, fixClock]
end Flapjack.Test.CakeFlatSemEvaluateExactParity
