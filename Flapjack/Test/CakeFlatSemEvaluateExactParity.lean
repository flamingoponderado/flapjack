module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateSource
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Semantics

@[expose] public section

/-! Unbounded flat evaluation compared with the original HOL observations in
`cake_flat_sem_evaluate_probe.out`. -/
namespace Flapjack.Test.CakeFlatSemEvaluateExactParity
open Flapjack.Compiler.Backend.FlatSem Flapjack.Compiler.Backend.FlatLang
open Flapjack.Basis.Pure.MlString

private def env : Environment Value := ⟨[]⟩
private def x := ofString "x"
private def call : Flapjack.Compiler.Backend.FlatLang.Exp := .app .none (.src .opapp)
  [.fn (ofString "unused") x (.varLocal .none x), .lit .none (.intLit 7)]

-- Original `semantics_empty` is proved by the pinned HOL probe.
example {C F : Type} (config : InstallConfig C) (ffi : Flapjack.HolFfiState F) :
    semantics config ffi [] = .terminate .success ffi.ioEvents := semantics_nil config ffi
example {C F : Type} (config : InstallConfig C) (ffi : Flapjack.HolFfiState F) :
    semantics config ffi [.lit .none (.intLit 1)] = .fail := semantics_nonunit_literal config ffi .none 1

example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 4 } [.lit .none (.intLit 3)] =
      ({ s with clock := 4 }, .val [.litv (.intLit 3)]) := by simp [evaluate]
example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 4 } [.varLocal .none x] =
      ({ s with clock := 4 }, .err (.abort .typeError)) := by simp [evaluate, env, x]
example {C F : Type} (s : State C F) :
    evaluate ⟨[(x, .litv (.intLit 1)), (x, .litv (.intLit 2))]⟩ { s with clock := 4 }
      [.varLocal .none x] = ({ s with clock := 4 }, .val [.litv (.intLit 1)]) := by
  simp [evaluate, x]
example {C F : Type} (s : State C F) :
    evaluate ⟨[(x, .litv (.intLit 1))]⟩ { s with clock := 4 }
      [.let_ .none (some x) (.lit .none (.intLit 2)) (.varLocal .none x)] =
        ({ s with clock := 4 }, .val [.litv (.intLit 2)]) := by
  simp [evaluate, fixClock, x]
example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 4 }
      [.if_ .none (.lit .none (.intLit 1)) (.lit .none (.intLit 2)) (.lit .none (.intLit 3))] =
        ({ s with clock := 4 }, .err (.abort .typeError)) := by
  simp [evaluate, fixClock, doIf]
example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 4 }
      [.raise .none (.lit .none (.intLit 9)), .lit .none (.intLit 2)] =
        ({ s with clock := 4 }, .err (.raise (.litv (.intLit 9)))) := by
  simp [evaluate, fixClock]
example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 4 }
      [.handle .none (.raise .none (.lit .none (.intLit 9))) []] =
        ({ s with clock := 4 }, .err (.raise (.litv (.intLit 9)))) := by
  simp [evaluate, fixClock, selectRow, pmatchRows]
example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 4 }
      [.handle .none (.raise .none (.lit .none (.intLit 8))) [(.pvar x, .varLocal .none x)]] =
        ({ s with clock := 4 }, .val [.litv (.intLit 8)]) := by
  rw [evaluate_handle_source]
  simp [evaluate_raise_source, evaluate_lit_source, evaluate_varLocal_source,
    Flapjack.holHd, fixClock, pmatchRows, pmatch, Flapjack.Compiler.Backend.FlatLang.patBindings, x]
example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 4 }
      [.letrec (ofString "trace")
        [(ofString "f", x, .lit .none (.intLit 1)), (ofString "f", ofString "y", .lit .none (.intLit 2))]
        (.lit .none (.intLit 3))] = ({ s with clock := 4 }, .err (.abort .typeError)) := by
  simp [evaluate]
example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 4 } [.app .none (.src .opapp) [.lit .none (.intLit 1)]] =
      ({ s with clock := 4 }, .err (.abort .typeError)) := by
  simp [evaluate, fixClock, doOpApp]
example {C F : Type} (s : State C F) :
    evaluate env { s with clock := 4 }
      [.mat .none (.lit .none (.intLit 1)) [(.pas (.pvar x) x, .lit .none (.intLit 3))]] =
        ({ s with clock := 4 }, .err (.abort .typeError)) := by
  rw [evaluate_mat_source]
  simp [evaluate_lit_source, fixClock, pmatchRows, pmatch, Flapjack.Compiler.Backend.FlatLang.patBindings]
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
  simp [evaluate, env, fixClock, applyResult, doApp, doAppNumeric, doAppMemory, Flapjack.SemanticPrimitivesHOL.storeAlloc]
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
