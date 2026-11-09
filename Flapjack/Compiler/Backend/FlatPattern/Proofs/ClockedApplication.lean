import Flapjack.SemanticPrimitivesProps.ResultRelation
import Flapjack.Compiler.Backend.FlatPattern.Proofs.ClockedExpressionList
import Flapjack.Compiler.Backend.FlatPattern.Proofs.SourceApplication
import Flapjack.Compiler.Backend.FlatPattern.Proofs.ThunkEvaluation
import Flapjack.Compiler.Backend.FlatPattern.Proofs.DynamicEvaluation

/-! Clock-bounded application simulation for the flat pattern pass. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)
open Flapjack.Basis.Pure.MlString (ofString)

/-- Flapjack induction step for nonrecursive primitive applications. -/
theorem compile_simpleApp_simulation_upTo {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (op : FlatLang.Op) (args : List FlatLang.Exp) (clock : Nat)
    (notCall : op ≠ .src .opapp) (notEval : op ≠ .src .eval)
    (notForce : op ≠ .src (.thunkOp .forceThunk))
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression) :
    ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock (.app trace op args) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n clockBound sourceEval envs states bound safe
  have argsBound : (compileExps cfg args).1 < n := by simpa [compileExp_app] using bound
  have reversedBound := compileExps_reverse_bound cfg args n argsBound
  have reversedIH : ∀ expression ∈ args.reverse, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression := by
    intro expression member
    exact argumentsIH expression (by simpa using member)
  have argsSim := compileExps_simulation_upTo cfg stateCfg clock args.reverse reversedIH
  have compiledReverse : (compileExps cfg args.reverse).2.2 = (compileExps cfg args).2.2.reverse := by
    simp [compileExps_rows, List.map_reverse]
  cases argsRun : FlatSem.evaluate sourceEnv source args.reverse with
  | mk sourceNext argsResult =>
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have outer := evaluate_app_args_error sourceEnv source sourceNext trace op args (.abort .typeError) argsRun
      rw [sourceEval] at outer
      exact safe (congrArg Prod.snd outer)
    obtain ⟨targetNext, targetArgsResult, targetArgsRun, nextStates, related⟩ := argsSim
      sourceEnv targetEnv source target sourceNext argsResult n clockBound argsRun envs states reversedBound argsSafe
    cases argsResult <;> cases targetArgsResult <;> simp only [SemanticPrimitivesProps.resultRel] at related
    case err.err leftError rightError =>
      have errorsRel := related
      have sourceOuter := evaluate_app_args_error sourceEnv source sourceNext trace op args leftError argsRun
      have targetOuter := evaluate_app_args_error targetEnv target targetNext trace op
        (compileExps cfg args).2.2 rightError (by simpa [compiledReverse] using targetArgsRun)
      have equal := sourceEval.symm.trans sourceOuter
      cases equal
      exact ⟨_, .err rightError, by simpa [compileExp_app] using targetOuter,
        stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, errorsRel⟩
    case val.val sourceValues targetValues =>
      have valuesRel := related
      let sourceFixed := { sourceNext with clock := min source.clock sourceNext.clock }
      let targetFixed := { targetNext with clock := min target.clock targetNext.clock }
      have fixedStates : StateRel stateCfg sourceFixed targetFixed :=
        stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates
      have sourceOuter := evaluate_simpleApp_values sourceEnv source sourceNext trace op args sourceValues notCall notEval notForce argsRun
      have targetOuter := evaluate_simpleApp_values targetEnv target targetNext trace op (compileExps cfg args).2.2
        targetValues notCall notEval notForce (by simpa [compiledReverse] using targetArgsRun)
      cases primitive : FlatSem.doApp sourceFixed op sourceValues.reverse with
      | none =>
        have bad : sourceResult = .err (.abort .typeError) := by
          have eq := sourceOuter.symm.trans sourceEval
          simpa [FlatSem.applyResult, sourceFixed, primitive] using (congrArg Prod.snd eq).symm
        exact (safe bad).elim
      | some outcome =>
        obtain ⟨sourceAfter, result⟩ := outcome
        obtain ⟨targetAfter, result', relation, afterStates, targetPrimitive⟩ := doApp_simulation
          sourceFixed sourceValues.reverse sourceAfter result targetFixed targetValues.reverse op stateCfg
          primitive ⟨fixedStates, List.forall₂_reverse_iff.mpr valuesRel⟩
        cases result with
        | val value =>
          cases result' with
          | err error' => exact False.elim relation
          | val value' =>
            have eq := sourceOuter.symm.trans sourceEval
            simp [FlatSem.applyResult, sourceFixed, primitive] at eq
            rcases eq with ⟨rfl, rfl⟩
            refine ⟨targetAfter, .val [_], ?_, afterStates, (.cons relation .nil)⟩
            simpa [compileExp_app, FlatSem.applyResult, targetFixed, targetPrimitive] using targetOuter
        | err error =>
          cases result' with
          | val value' => exact False.elim relation
          | err error' =>
            have eq := sourceOuter.symm.trans sourceEval
            simp [FlatSem.applyResult, sourceFixed, primitive] at eq
            rcases eq with ⟨rfl, rfl⟩
            refine ⟨targetAfter, .err error', ?_, afterStates, relation⟩
            simpa [compileExp_app, FlatSem.applyResult, targetFixed, targetPrimitive] using targetOuter


/-- Calls simulate their selected closure body, using an induction hypothesis
for arbitrary compiled closure bodies at smaller clocks. -/
theorem compile_call_simulation_at_clock_boundedArgs {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (args : List FlatLang.Exp) (clock : Nat)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression)
    (callIH : ∀ (bodyCfg : Config) (body : FlatLang.Exp)
      (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value)
      (source target sourceFinal : FlatSem.State C F) (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
      source.clock < clock → FlatSem.evaluate sourceEnv source [body] = (sourceFinal, sourceResult) →
      EnvRel n sourceEnv targetEnv → StateRel stateCfg source target → (compileExp bodyCfg body).1 < n →
      sourceResult ≠ .err (.abort .typeError) →
      ∃ targetFinal targetResult, FlatSem.evaluate targetEnv target [(compileExp bodyCfg body).2.2] =
        (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal ∧ SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel sourceResult targetResult) :
    ∀ (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (source target sourceFinal : FlatSem.State C F)
      (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
      source.clock = clock →
      FlatSem.evaluate sourceEnv source [.app trace (.src .opapp) args] = (sourceFinal, sourceResult) →
      EnvRel n sourceEnv targetEnv → StateRel stateCfg source target →
      (compileExp cfg (.app trace (.src .opapp) args)).1 < n →
      sourceResult ≠ .err (.abort .typeError) →
      ∃ targetFinal targetResult,
        FlatSem.evaluate targetEnv target [(compileExp cfg (.app trace (.src .opapp) args)).2.2] =
          (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal ∧ SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel sourceResult targetResult := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n clockEq sourceEval envs states bound safe
  have argsBound : (compileExps cfg args).1 < n := by simpa [compileExp_app] using bound
  have reversedBound := compileExps_reverse_bound cfg args n argsBound
  have reversedIH : ∀ expression ∈ args.reverse, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression := by
    intro expression member
    exact argumentsIH expression (by simpa using member)
  have argsSim := compileExps_simulation_upTo cfg stateCfg clock args.reverse reversedIH
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
      sourceEnv targetEnv source target sourceNext argsResult n (by omega) argsRun envs states reversedBound argsSafe
    cases argsResult <;> cases targetArgsResult <;> simp only [SemanticPrimitivesProps.resultRel] at related
    case err.err leftError rightError =>
      have errorsRel := related
      have sourceOuter := evaluate_app_args_error sourceEnv source sourceNext trace (.src .opapp) args leftError argsRun
      have targetOuter := evaluate_app_args_error targetEnv target targetNext trace (.src .opapp)
        (compileExps cfg args).2.2 rightError (by simpa [compiledReverse] using targetArgsRun)
      have equal := sourceEval.symm.trans sourceOuter
      cases equal
      exact ⟨_, .err rightError, by simpa [compileExp_app] using targetOuter,
        stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, errorsRel⟩
    case val.val sourceValues targetValues =>
      have valuesRel := related
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
          doOpApp_simulation_reverse sourceValues callEnv body targetValues ⟨call, valuesRel⟩
        have targetClock : targetFixed.clock = sourceFixed.clock := fixedStates.1
        by_cases zero : sourceFixed.clock = 0
        · have targetZero : targetFixed.clock = 0 := by omega
          have sourceOuter := evaluate_call_timeout sourceEnv source sourceNext trace args sourceValues callEnv body argsRun call zero
          have targetOuter := evaluate_call_timeout targetEnv target targetNext trace (compileExps cfg args).2.2 targetValues
            targetCallEnv compiledBody (by simpa [compiledReverse] using targetArgsRun) targetCall targetZero
          have equal := sourceEval.symm.trans sourceOuter
          cases equal
          exact ⟨_, .err (.abort .timeoutError), by simpa [compileExp_app] using targetOuter, fixedStates, rfl⟩
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


/-- Forcing preserves the forward simulation, using the induction hypotheses
for the arguments and the smaller generated application. -/
theorem compile_force_simulation_at_clock_boundedArgs {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (args : List FlatLang.Exp) (clock : Nat)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression)
    (bodyIH : ∀ (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value)
      (source target sourceFinal : FlatSem.State C F) (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
      source.clock ≤ clock →
      FlatSem.evaluate sourceEnv source [FlatSem.appUnit (.varLocal .none (ofString "f"))] = (sourceFinal, sourceResult) →
      EnvRel n sourceEnv targetEnv → StateRel stateCfg source target →
      (compileExp cfg (FlatSem.appUnit (.varLocal .none (ofString "f")))).1 < n →
      sourceResult ≠ .err (.abort .typeError) →
      ∃ targetFinal targetResult,
        FlatSem.evaluate targetEnv target [(compileExp cfg (FlatSem.appUnit (.varLocal .none (ofString "f")))).2.2] =
          (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal ∧ SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel sourceResult targetResult) :
    ∀ (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (source target sourceFinal : FlatSem.State C F)
      (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
      source.clock = clock →
      FlatSem.evaluate sourceEnv source [.app trace (.src (.thunkOp .forceThunk)) args] = (sourceFinal, sourceResult) →
      EnvRel n sourceEnv targetEnv → StateRel stateCfg source target →
      (compileExp cfg (.app trace (.src (.thunkOp .forceThunk)) args)).1 < n →
      sourceResult ≠ .err (.abort .typeError) →
      ∃ targetFinal targetResult,
        FlatSem.evaluate targetEnv target [(compileExp cfg (.app trace (.src (.thunkOp .forceThunk)) args)).2.2] =
          (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal ∧ SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel sourceResult targetResult := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n clockEq sourceEval envs states bound safe
  have argsBound : (compileExps cfg args).1 < n := by simpa [compileExp_app] using bound
  have reversedBound := compileExps_reverse_bound cfg args n argsBound
  have reversedIH : ∀ expression ∈ args.reverse, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression := by
    intro expression member
    exact argumentsIH expression (by simpa using member)
  have argsSim := compileExps_simulation_upTo cfg stateCfg clock args.reverse reversedIH
  have compiledReverse : (compileExps cfg args.reverse).2.2 = (compileExps cfg args).2.2.reverse := by
    simp [compileExps_rows, List.map_reverse]
  cases argsRun : FlatSem.evaluate sourceEnv source args.reverse with
  | mk sourceNext argsResult =>
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have outer := evaluate_app_args_error sourceEnv source sourceNext trace (.src (.thunkOp .forceThunk)) args (.abort .typeError) argsRun
      rw [sourceEval] at outer
      exact safe (congrArg Prod.snd outer)
    obtain ⟨targetNext, targetArgsResult, targetArgsRun, nextStates, related⟩ := argsSim
      sourceEnv targetEnv source target sourceNext argsResult n (by omega) argsRun envs states reversedBound argsSafe
    cases argsResult <;> cases targetArgsResult <;> simp only [SemanticPrimitivesProps.resultRel] at related
    case err.err leftError rightError =>
      have errorsRel := related
      have sourceOuter := evaluate_app_args_error sourceEnv source sourceNext trace (.src (.thunkOp .forceThunk)) args leftError argsRun
      have targetOuter := evaluate_app_args_error targetEnv target targetNext trace (.src (.thunkOp .forceThunk))
        (compileExps cfg args).2.2 rightError (by simpa [compiledReverse] using targetArgsRun)
      have equal := sourceEval.symm.trans sourceOuter
      cases equal
      exact ⟨_, .err rightError, by simpa [compileExp_app] using targetOuter,
        stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, errorsRel⟩
    case val.val sourceValues targetValues =>
      have valuesRel := related
      have targetArgsRun' : FlatSem.evaluate targetEnv target (compileExps cfg args).2.2.reverse =
          (targetNext, .val targetValues) := by simpa [compiledReverse] using targetArgsRun
      let sourceFixed := { sourceNext with clock := min source.clock sourceNext.clock }
      let targetFixed := { targetNext with clock := min target.clock targetNext.clock }
      have fixedStates : StateRel stateCfg sourceFixed targetFixed :=
        stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates
      have inspected := destThunk_related valuesRel fixedStates.2.1
      cases thunk : FlatSem.destThunk sourceValues sourceFixed.refs with
      | badRef | notThunk =>
        simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, sourceFixed, thunk] at sourceEval
        exact (safe sourceEval.2.symm).elim
      | isThunk mode value =>
        cases targetThunk : FlatSem.destThunk targetValues targetFixed.refs with
        | badRef | notThunk => simp [thunk, targetThunk, DestThunkRel] at inspected
        | isThunk targetMode targetValue =>
          have pair : mode = targetMode ∧ ValueRel value targetValue := by
            simpa [thunk, targetThunk, DestThunkRel] using inspected
          rcases pair with ⟨rfl, valueRelated⟩
          cases mode with
          | evaluated =>
            simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, sourceFixed, thunk] at sourceEval
            rcases sourceEval with ⟨rfl, rfl⟩
            refine ⟨targetFixed, .val [targetValue], ?_, fixedStates, (.cons valueRelated .nil)⟩
            simp [compileExp_app, FlatSem.evaluate, targetArgsRun', FlatSem.fixClock, targetFixed, targetThunk]
          | notEvaluated =>
            let body := FlatSem.appUnit (.varLocal .none (ofString "f"))
            let bodyEnv : FlatSem.Environment FlatSem.Value := ⟨[(ofString "f", value)]⟩
            let bodyEnv' : FlatSem.Environment FlatSem.Value := ⟨[(ofString "f", targetValue)]⟩
            cases bodyRun : FlatSem.evaluate bodyEnv sourceFixed [body] with
            | mk sourceLast bodyResult =>
              have bodyRun' : FlatSem.evaluate ⟨[(ofString "f", value)]⟩
                  { sourceNext with clock := min source.clock sourceNext.clock }
                  [FlatSem.appUnit (.varLocal .none (ofString "f"))] = (sourceLast, bodyResult) := bodyRun
              have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
                intro bad
                subst bodyResult
                simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, sourceFixed, thunk, bodyRun'] at sourceEval
                exact safe sourceEval.2.symm
              let m := (compileExp cfg body).1 + 1
              have clockBound : sourceFixed.clock ≤ clock := by
                simp [sourceFixed, clockEq]
              obtain ⟨targetLast, targetResult, targetBodyRun, lastStates, resultRel⟩ := bodyIH
                bodyEnv bodyEnv' sourceFixed targetFixed sourceLast bodyResult m clockBound bodyRun
                (forceBody_envRel m value targetValue valueRelated) fixedStates (by simp [m, body]) bodySafe
              have targetBody : FlatSem.evaluate bodyEnv' targetFixed [body] = (targetLast, targetResult) := by
                simpa [body, compile_forceBody] using targetBodyRun
              have targetBody' : FlatSem.evaluate ⟨[(ofString "f", targetValue)]⟩
                  { targetNext with clock := min target.clock targetNext.clock }
                  [FlatSem.appUnit (.varLocal .none (ofString "f"))] = (targetLast, targetResult) := targetBody
              cases bodyResult <;> cases targetResult <;> simp only [SemanticPrimitivesProps.resultRel] at resultRel
              case err.err leftError rightError =>
                have errors := resultRel
                simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, sourceFixed, thunk, bodyRun'] at sourceEval
                rcases sourceEval with ⟨rfl, rfl⟩
                refine ⟨targetLast, .err rightError, ?_, lastStates, errors⟩
                simp [compileExp_app, FlatSem.evaluate, targetArgsRun', FlatSem.fixClock,
                  targetFixed, targetThunk, targetBody']
              case val.val leftValues rightValues =>
                have results := resultRel
                cases updated : FlatSem.updateThunk sourceValues sourceLast.refs leftValues with
                | none =>
                  simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, sourceFixed, thunk, bodyRun', updated] at sourceEval
                  exact (safe sourceEval.2.symm).elim
                | some refs =>
                  obtain ⟨refs', updated', refsRel⟩ := updateThunk_related valuesRel results lastStates.2.1 updated
                  simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, sourceFixed, thunk, bodyRun', updated] at sourceEval
                  rcases sourceEval with ⟨rfl, rfl⟩
                  refine ⟨{ targetLast with refs := refs' }, .val rightValues, ?_, ?_, results⟩
                  · simp [compileExp_app, FlatSem.evaluate, targetArgsRun', FlatSem.fixClock,
                      targetFixed, targetThunk, targetBody', updated']
                  · exact ⟨lastStates.1, refsRel, lastStates.2.2⟩

/-- Dynamic evaluation simulates installed declarations using the
smaller-clock declaration induction hypothesis. -/
theorem compile_eval_simulation_at_clock_boundedArgs {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (args : List FlatLang.Exp) (clock : Nat)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression)
    (decsIH : ∀ (source target sourceFinal : FlatSem.State C F) (declarations : List FlatLang.Exp)
      (outcome : Option (SemanticPrimitivesHOL.ErrorResult FlatSem.Value)),
      source.clock < clock → FlatSem.evaluateDecs source declarations = (sourceFinal, outcome) →
      StateRel stateCfg source target → outcome ≠ some (.abort .typeError) →
      ∃ targetFinal targetOutcome, FlatSem.evaluateDecs target (declarations.map (compileDec stateCfg)) =
        (targetFinal, targetOutcome) ∧ StateRel stateCfg sourceFinal targetFinal ∧ optionRel (SemanticPrimitivesProps.excRel ValueRel) outcome targetOutcome) :
    ∀ (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (source target sourceFinal : FlatSem.State C F)
      (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
      source.clock = clock →
      FlatSem.evaluate sourceEnv source [.app trace (.src .eval) args] = (sourceFinal, sourceResult) →
      EnvRel n sourceEnv targetEnv → StateRel stateCfg source target →
      (compileExp cfg (.app trace (.src .eval) args)).1 < n →
      sourceResult ≠ .err (.abort .typeError) →
      ∃ targetFinal targetResult,
        FlatSem.evaluate targetEnv target [(compileExp cfg (.app trace (.src .eval) args)).2.2] =
          (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal ∧ SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel sourceResult targetResult := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n clockEq sourceEval envs states bound safe
  have argsBound : (compileExps cfg args).1 < n := by simpa [compileExp_app] using bound
  have reversedBound := compileExps_reverse_bound cfg args n argsBound
  have reversedIH : ∀ expression ∈ args.reverse, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression := by
    intro expression member
    exact argumentsIH expression (by simpa using member)
  have argsSim := compileExps_simulation_upTo cfg stateCfg clock args.reverse reversedIH
  have compiledReverse : (compileExps cfg args.reverse).2.2 = (compileExps cfg args).2.2.reverse := by
    simp [compileExps_rows, List.map_reverse]
  cases argsRun : FlatSem.evaluate sourceEnv source args.reverse with
  | mk sourceNext argsResult =>
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have outer := evaluate_app_args_error sourceEnv source sourceNext trace (.src .eval) args (.abort .typeError) argsRun
      rw [sourceEval] at outer
      exact safe (congrArg Prod.snd outer)
    obtain ⟨targetNext, targetArgsResult, targetArgsRun, nextStates, related⟩ := argsSim
      sourceEnv targetEnv source target sourceNext argsResult n (by omega) argsRun envs states reversedBound argsSafe
    cases argsResult <;> cases targetArgsResult <;> simp only [SemanticPrimitivesProps.resultRel] at related
    case err.err leftError rightError =>
      have errorsRel := related
      have sourceOuter := evaluate_app_args_error sourceEnv source sourceNext trace (.src .eval) args leftError argsRun
      have targetOuter := evaluate_app_args_error targetEnv target targetNext trace (.src .eval)
        (compileExps cfg args).2.2 rightError (by simpa [compiledReverse] using targetArgsRun)
      have equal := sourceEval.symm.trans sourceOuter
      cases equal
      exact ⟨_, .err rightError, by simpa [compileExp_app] using targetOuter,
        stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, errorsRel⟩
    case val.val sourceValues targetValues =>
      have valuesRel := related
      let sourceFixed := { sourceNext with clock := min source.clock sourceNext.clock }
      let targetFixed := { targetNext with clock := min target.clock targetNext.clock }
      have fixedStates : StateRel stateCfg sourceFixed targetFixed :=
        stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates
      cases decoded : FlatSem.doEval sourceValues.reverse sourceNext.evalConfig with
      | none =>
        have bad := evaluate_eval_bad sourceEnv source sourceNext trace args sourceValues argsRun decoded
        rw [sourceEval] at bad
        exact (safe (congrArg Prod.snd bad)).elim
      | some payload =>
        obtain ⟨declarations, sourceConfig, result⟩ := payload
        obtain ⟨targetConfig, targetValue, targetDecoded, installedStates, valueRel⟩ :=
          doEval_state_simulation stateCfg sourceFixed targetFixed sourceValues.reverse targetValues.reverse fixedStates
            (List.forall₂_reverse_iff.mpr valuesRel) declarations sourceConfig result decoded
        have targetClock : targetFixed.clock = sourceFixed.clock := fixedStates.1
        by_cases zero : sourceFixed.clock = 0
        · have targetZero : targetFixed.clock = 0 := by omega
          have sourceOuter := evaluate_eval_timeout sourceEnv source sourceNext trace args sourceValues declarations
            sourceConfig result argsRun decoded zero
          have targetOuter := evaluate_eval_timeout targetEnv target targetNext trace (compileExps cfg args).2.2 targetValues
            (declarations.map (compileDec stateCfg)) targetConfig targetValue
            (by simpa [compiledReverse] using targetArgsRun) targetDecoded targetZero
          have equal := sourceEval.symm.trans sourceOuter
          cases equal
          exact ⟨_, .err (.abort .timeoutError), by simpa [compileExp_app] using targetOuter, installedStates, rfl⟩
        · have targetNonzero : targetFixed.clock ≠ 0 := by omega
          let sourceInstalled := { sourceFixed with evalConfig := sourceConfig }
          let targetInstalled := { targetFixed with evalConfig := targetConfig }
          have smaller : (FlatSem.decClock sourceInstalled).clock < clock := by
            have clamped := Nat.min_le_left source.clock sourceNext.clock
            have positive : 0 < min source.clock sourceNext.clock := Nat.pos_of_ne_zero zero
            simp only [FlatSem.decClock, sourceInstalled, sourceFixed]
            omega
          have declStates := stateRel_decClock stateCfg sourceInstalled targetInstalled installedStates
          cases declsRun : FlatSem.evaluateDecs (FlatSem.decClock sourceInstalled) declarations with
          | mk sourceLast outcome =>
            have outcomeSafe : outcome ≠ some (.abort .typeError) := by
              intro bad
              subst outcome
              have sourceOuter := evaluate_eval_declarations sourceEnv source sourceNext sourceLast trace args sourceValues
                declarations sourceConfig result (some (.abort .typeError)) argsRun decoded zero declsRun
              rw [sourceEval] at sourceOuter
              exact safe (congrArg Prod.snd sourceOuter)
            obtain ⟨targetLast, targetOutcome, targetDeclsRun, finalRel, outcomeRel⟩ := decsIH
              (FlatSem.decClock sourceInstalled) (FlatSem.decClock targetInstalled) sourceLast declarations outcome
              smaller declsRun declStates outcomeSafe
            cases outcome with
            | none =>
              cases targetOutcome with
              | some error => simp [optionRel] at outcomeRel
              | none =>
                have sourceOuter := evaluate_eval_declarations sourceEnv source sourceNext sourceLast trace args sourceValues
                  declarations sourceConfig result none argsRun decoded zero declsRun
                have targetOuter := evaluate_eval_declarations targetEnv target targetNext targetLast trace (compileExps cfg args).2.2
                  targetValues (declarations.map (compileDec stateCfg)) targetConfig targetValue none
                  (by simpa [compiledReverse] using targetArgsRun) targetDecoded targetNonzero targetDeclsRun
                have equal := sourceEval.symm.trans sourceOuter
                cases equal
                exact ⟨targetLast, .val [targetValue], by simpa [compileExp_app] using targetOuter, finalRel, (.cons valueRel .nil)⟩
            | some error =>
              cases targetOutcome with
              | none => simp [optionRel] at outcomeRel
              | some targetError =>
                have errorsRel : SemanticPrimitivesProps.excRel ValueRel error targetError := by
                  simpa [optionRel] using outcomeRel
                have sourceOuter := evaluate_eval_declarations sourceEnv source sourceNext sourceLast trace args sourceValues
                  declarations sourceConfig result (some error) argsRun decoded zero declsRun
                have targetOuter := evaluate_eval_declarations targetEnv target targetNext targetLast trace (compileExps cfg args).2.2
                  targetValues (declarations.map (compileDec stateCfg)) targetConfig targetValue (some targetError)
                  (by simpa [compiledReverse] using targetArgsRun) targetDecoded targetNonzero targetDeclsRun
                have equal := sourceEval.symm.trans sourceOuter
                cases equal
                exact ⟨targetLast, .err targetError, by simpa [compileExp_app] using targetOuter, finalRel, errorsRel⟩

end Flapjack.Compiler.Backend.FlatPattern
