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

/-- Calls simulate their selected closure body, using an induction hypothesis
for arbitrary compiled closure bodies at smaller clocks. -/
theorem compile_call_simulation_at_clock {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (args : List FlatLang.Exp) (clock : Nat)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression)
    (callIH : ∀ (bodyCfg : Config) (body : FlatLang.Exp)
      (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value)
      (source target sourceFinal : FlatSem.State C F) (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
      source.clock < clock → FlatSem.evaluate sourceEnv source [body] = (sourceFinal, sourceResult) →
      EnvRel n sourceEnv targetEnv → StateRel stateCfg source target → (compileExp bodyCfg body).1 < n →
      sourceResult ≠ .err (.abort .typeError) →
      ∃ targetFinal targetResult, FlatSem.evaluate targetEnv target [(compileExp bodyCfg body).2.2] =
        (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult) :
    ∀ (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (source target sourceFinal : FlatSem.State C F)
      (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
      source.clock = clock →
      FlatSem.evaluate sourceEnv source [.app trace (.src .opapp) args] = (sourceFinal, sourceResult) →
      EnvRel n sourceEnv targetEnv → StateRel stateCfg source target →
      (compileExp cfg (.app trace (.src .opapp) args)).1 < n →
      sourceResult ≠ .err (.abort .typeError) →
      ∃ targetFinal targetResult,
        FlatSem.evaluate targetEnv target [(compileExp cfg (.app trace (.src .opapp) args)).2.2] =
          (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n clockEq sourceEval envs states bound safe
  have argsBound : (compileExps cfg args).1 < n := by simpa [compileExp_app] using bound
  have reversedBound := compileExps_reverse_bound cfg args n argsBound
  have reversedIH : ∀ expression ∈ args.reverse, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression := by
    intro expression member
    exact argumentsIH expression (by simpa using member)
  have argsSim := compileExps_simulation cfg stateCfg args.reverse reversedIH
  have compiledReverse : (compileExps cfg args.reverse).2.2 = (compileExps cfg args).2.2.reverse := by
    simp [compileExps_rows, List.map_reverse]
  cases argsRun : FlatSem.evaluate sourceEnv source args.reverse with
  | mk sourceNext argsResult =>
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have outer := evaluate_app_args_error sourceEnv source sourceNext trace (.src .opapp) args (.abort .typeError) argsRun
      rw [sourceEval] at outer
      exact safe (congrArg Prod.snd outer)
    obtain ⟨targetNext, targetArgsResult, targetArgsRun, nextStates, related⟩ := argsSim
      sourceEnv targetEnv source target sourceNext argsResult n argsRun envs states reversedBound argsSafe
    cases related with
    | error errorsRel =>
      rename_i leftError rightError
      have sourceOuter := evaluate_app_args_error sourceEnv source sourceNext trace (.src .opapp) args leftError argsRun
      have targetOuter := evaluate_app_args_error targetEnv target targetNext trace (.src .opapp)
        (compileExps cfg args).2.2 rightError (by simpa [compiledReverse] using targetArgsRun)
      have equal := sourceEval.symm.trans sourceOuter
      cases equal
      exact ⟨_, _, by simpa [compileExp_app] using targetOuter,
        stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, .error errorsRel⟩
    | values valuesRel =>
      rename_i sourceValues targetValues
      let sourceFixed := { sourceNext with clock := min source.clock sourceNext.clock }
      let targetFixed := { targetNext with clock := min target.clock targetNext.clock }
      have fixedStates : StateRel stateCfg sourceFixed targetFixed :=
        stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates
      cases call : FlatSem.doOpApp sourceValues.reverse with
      | none =>
        have bad := evaluate_call_bad sourceEnv source sourceNext trace args sourceValues argsRun call
        rw [sourceEval] at bad
        exact (safe (congrArg Prod.snd bad)).elim
      | some selected =>
        obtain ⟨callEnv, body⟩ := selected
        obtain ⟨bodyBound, flag, compiledBody, targetCallEnv, bodyCfg, bodyCompiled, callEnvs, targetCall⟩ :=
          doOpApp_simulation sourceValues.reverse targetValues.reverse callEnv body call (valueRel_reverse valuesRel)
        have targetClock : targetFixed.clock = sourceFixed.clock := fixedStates.1
        by_cases zero : sourceFixed.clock = 0
        · have targetZero : targetFixed.clock = 0 := by omega
          have sourceOuter := evaluate_call_timeout sourceEnv source sourceNext trace args sourceValues callEnv body argsRun call zero
          have targetOuter := evaluate_call_timeout targetEnv target targetNext trace (compileExps cfg args).2.2 targetValues
            targetCallEnv compiledBody (by simpa [compiledReverse] using targetArgsRun) targetCall targetZero
          have equal := sourceEval.symm.trans sourceOuter
          cases equal
          exact ⟨_, _, by simpa [compileExp_app] using targetOuter, fixedStates, .error (.abort .timeoutError)⟩
        · have targetNonzero : targetFixed.clock ≠ 0 := by omega
          have sourceOuter := evaluate_call_body sourceEnv source sourceNext trace args sourceValues callEnv body argsRun call zero
          have targetOuter := evaluate_call_body targetEnv target targetNext trace (compileExps cfg args).2.2 targetValues
            targetCallEnv compiledBody (by simpa [compiledReverse] using targetArgsRun) targetCall targetNonzero
          have smaller : (FlatSem.decClock sourceFixed).clock < clock := by
            have clamped := Nat.min_le_left source.clock sourceNext.clock
            have positive : 0 < min source.clock sourceNext.clock := by
              apply Nat.pos_of_ne_zero
              exact zero
            simp only [FlatSem.decClock, sourceFixed]
            omega
          have callStates := stateRel_decClock stateCfg sourceFixed targetFixed fixedStates
          have sourceBody := sourceOuter.symm.trans sourceEval
          obtain ⟨targetFinal, output, bodyRun, finalRel, resultRel⟩ := callIH bodyCfg body callEnv targetCallEnv
            (FlatSem.decClock sourceFixed) (FlatSem.decClock targetFixed) sourceFinal sourceResult (bodyBound + 1)
            smaller sourceBody callEnvs callStates (by simp [bodyCompiled]) safe
          refine ⟨targetFinal, output, ?_, finalRel, resultRel⟩
          have targetBody : FlatSem.evaluate targetCallEnv (FlatSem.decClock targetFixed) [compiledBody] =
              (targetFinal, output) := by simpa [bodyCompiled] using bodyRun
          simpa [compileExp_app, targetOuter] using targetBody

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
