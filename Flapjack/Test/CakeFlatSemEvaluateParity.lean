import Flapjack.Compiler.Backend.Semantics.FlatSem.Evaluate

/-! Matched observations from `cake_flat_sem_evaluate_probe.out`. The fuel
bound is separate from the original evaluator's clock. -/
namespace Flapjack.Test.CakeFlatSemEvaluateParity
open Flapjack.Compiler.Backend.FlatSem Flapjack.Compiler.Backend.FlatLang
open Flapjack.Basis.Pure.MlString

private def env : Environment Value := ⟨[]⟩
private def x := ofString "x"
private def call : Flapjack.Compiler.Backend.FlatLang.Exp := .app .none (.src .opapp)
  [.fn (ofString "unused") x (.varLocal .none x), .lit .none (.intLit 7)]

example {C F : Type} (s : State C F) :
    evaluateFuel 5 env { s with clock := 4 } [.lit .none (.intLit 3)] =
      some ({ s with clock := 4 }, .val [.litv (.intLit 3)]) := by rfl
example {C F : Type} (s : State C F) :
    evaluateFuel 5 env { s with clock := 4 } [.varLocal .none x] =
      some ({ s with clock := 4 }, .err (.abort .typeError)) := by rfl
example {C F : Type} (s : State C F) :
    evaluateFuel 20 env { s with clock := 4 } [call] =
      some ({ s with clock := 3 }, .val [.litv (.intLit 7)]) := by rfl
example {C F : Type} (s : State C F) :
    evaluateFuel 20 env { s with clock := 0 } [call] =
      some ({ s with clock := 0 }, .err (.abort .timeoutError)) := by rfl
example {C F : Type} (s : State C F) :
    evaluateFuel 20 env { s with clock := 4 }
      [.handle .none (.raise .none (.lit .none (.intLit 8))) [(.pvar x, .varLocal .none x)]] =
      some ({ s with clock := 4 }, .val [.litv (.intLit 8)]) := by
  simp [evaluateFuel, selectRow, pmatchRows, pmatch, patBindings, env, x, fixClock]
example {C F : Type} (s : State C F) :
    evaluateFuel 30 env { s with clock := 4, refs := [] }
      [.con .none none [.app .none (.src .opref) [.lit .none (.intLit 1)],
        .app .none (.src .opref) [.lit .none (.intLit 2)]]] =
      some ({ s with clock := 4, refs := [.refv (.litv (.intLit 2)), .refv (.litv (.intLit 1))] },
        .val [.conv none [.loc true 1, .loc true 0]]) := by rfl
example {C F : Type} (s : State C F) :
    evaluateFuel 10 env { s with clock := 4 } [.mat .none (.lit .none (.intLit 1)) []] =
      some ({ s with clock := 4 }, .err (.raise bindExnV)) := by rfl
example {C F : Type} (s : State C F) :
    evaluateFuel 0 env s [.lit .none (.intLit 3)] = none := by rfl
example {C F : Type} (s : State C F) :
    evaluateFuel 30 ⟨[(ofString "t", .loc false 0)]⟩
      { s with clock := 4, refs := [.thunk .notEvaluated (.closure env (ofString "u") (.lit .none (.intLit 5)))] }
      [.app .none (.src (.thunkOp .forceThunk)) [.varLocal .none (ofString "t")]] =
      some ({ s with clock := 3, refs := [.thunk .evaluated (.litv (.intLit 5))] }, .val [.litv (.intLit 5)]) := by rfl
example {C F : Type} (s : State C F) :
    evaluateDecsFuel 10 { s with clock := 4 } [.con .none none []] = some ({ s with clock := 4 }, none) := by rfl
example {C F : Type} (s : State C F) :
    evaluateDecsFuel 10 { s with clock := 4 } [.lit .none (.intLit 1)] =
      some ({ s with clock := 4 }, some (.abort .typeError)) := by rfl
end Flapjack.Test.CakeFlatSemEvaluateParity
