import Flapjack.Compiler.Backend.FlatPattern.Proofs.ExpressionList

/-! Function application for the flat pattern compiler. The evaluator and
proof-side value/state relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Application compilation keeps the operator and compiles its arguments. -/
theorem compileExp_app (cfg : Config) (trace : BackendCommon.Tra) (op : FlatLang.Op)
    (args : List FlatLang.Exp) :
    (compileExp cfg (.app trace op args)).1 = (compileExps cfg args).1 ∧
    (compileExp cfg (.app trace op args)).2.2 = .app trace op (compileExps cfg args).2.2 := by
  cases compiled : compileExps cfg args with
  | mk bound rest => cases rest with | mk flag output => simp [compileExp, compiled]

/-- An argument-evaluation error propagates through an application. -/
theorem evaluate_app_args_error {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (op : FlatLang.Op)
    (args : List FlatLang.Exp) (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .err error)) :
    FlatSem.evaluate env state [.app trace op args] =
      ({ next with clock := min state.clock next.clock }, .err error) := by
  simp [FlatSem.evaluate, argsRun, FlatSem.fixClock]

/-- A function application with invalid operands fails with a type error. -/
theorem evaluate_call_bad {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (values : List FlatSem.Value)
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .val values))
    (call : FlatSem.doOpApp values.reverse = none) :
    FlatSem.evaluate env state [.app trace (.src .opapp) args] =
      ({ next with clock := min state.clock next.clock }, .err (.abort .typeError)) := by
  simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, call]

/-- A valid function call at zero clock times out before entering its body. -/
theorem evaluate_call_timeout {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (values : List FlatSem.Value) (callEnv : FlatSem.Environment FlatSem.Value) (body : FlatLang.Exp)
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .val values))
    (call : FlatSem.doOpApp values.reverse = some (callEnv, body))
    (zero : min state.clock next.clock = 0) :
    FlatSem.evaluate env state [.app trace (.src .opapp) args] =
      ({ next with clock := min state.clock next.clock }, .err (.abort .timeoutError)) := by
  simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, call, zero]

/-- A valid function call with remaining clock evaluates its selected body. -/
theorem evaluate_call_body {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (values : List FlatSem.Value) (callEnv : FlatSem.Environment FlatSem.Value) (body : FlatLang.Exp)
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .val values))
    (call : FlatSem.doOpApp values.reverse = some (callEnv, body))
    (positive : min state.clock next.clock ≠ 0) :
    FlatSem.evaluate env state [.app trace (.src .opapp) args] =
      FlatSem.evaluate callEnv (FlatSem.decClock { next with clock := min state.clock next.clock }) [body] := by
  simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, call, positive]

/-- If application arguments fail, the compiler preserves the error without
executing the operator. -/
theorem compile_app_args_error {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (op : FlatLang.Op) (args : List FlatLang.Exp) (n : Nat)
    (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (source target sourceNext : FlatSem.State C F)
    (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression)
    (argsRun : FlatSem.evaluate sourceEnv source args.reverse = (sourceNext, .err error))
    (envs : EnvRel n sourceEnv targetEnv) (states : StateRel stateCfg source target)
    (bound : (compileExp cfg (.app trace op args)).1 < n) (safe : error ≠ .abort .typeError) :
    ∃ (targetNext : FlatSem.State C F) (targetError : SemanticPrimitivesHOL.ErrorResult FlatSem.Value),
      FlatSem.evaluate sourceEnv source [.app trace op args] =
        ({ sourceNext with clock := min source.clock sourceNext.clock }, .err error) ∧
      FlatSem.evaluate targetEnv target [(compileExp cfg (.app trace op args)).2.2] =
        ({ targetNext with clock := min target.clock targetNext.clock }, .err targetError) ∧
      StateRel stateCfg { sourceNext with clock := min source.clock sourceNext.clock }
        { targetNext with clock := min target.clock targetNext.clock } ∧ FlatErrorRel error targetError := by
  have argsBound : (compileExps cfg args).1 < n := by simpa [compileExp_app] using bound
  have reversedBound := compileExps_reverse_bound cfg args n argsBound
  have reversedIH : ∀ expression ∈ args.reverse, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression := by
    intro expression member
    exact argumentsIH expression (by simpa using member)
  have argsSim := compileExps_simulation cfg stateCfg args.reverse reversedIH
  obtain ⟨targetNext, targetResult, targetArgsRun, nextStates, related⟩ := argsSim
    sourceEnv targetEnv source target sourceNext (.err error) n argsRun envs states reversedBound (by simpa using safe)
  cases related with
  | error errorsRel =>
    rename_i targetError
    have compiledReverse : (compileExps cfg args.reverse).2.2 = (compileExps cfg args).2.2.reverse := by
      simp [compileExps_rows, List.map_reverse]
    have sourceOuter := evaluate_app_args_error sourceEnv source sourceNext trace op args error argsRun
    have targetOuter := evaluate_app_args_error targetEnv target targetNext trace op (compileExps cfg args).2.2
      targetError (by simpa [compiledReverse] using targetArgsRun)
    exact ⟨targetNext, targetError, sourceOuter, by simpa [compileExp_app] using targetOuter,
      stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, errorsRel⟩

end Flapjack.Compiler.Backend.FlatPattern
