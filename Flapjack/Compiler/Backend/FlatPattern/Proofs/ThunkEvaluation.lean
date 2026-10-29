import Flapjack.Compiler.Backend.FlatPattern.Proofs.FunctionApplication
import Flapjack.Compiler.Backend.FlatPattern.Proofs.ThunkRelation

/-! Thunk forcing for the flat pattern compiler. The evaluator and proof-side
relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)
open Flapjack.Basis.Pure.MlString (ofString)

/-- The generated call for forcing a thunk is unchanged by compilation. -/
theorem compile_forceBody (cfg : Config) :
    (compileExp cfg (FlatSem.appUnit (.varLocal .none (ofString "f")))).2.2 =
      FlatSem.appUnit (.varLocal .none (ofString "f")) := by
  simp [FlatSem.appUnit, compileExp, compileExps]

/-- The environments constructed for forcing related thunks are related at
every name bound. -/
theorem forceBody_envRel (n : Nat) (value value' : FlatSem.Value) (related : ValueRel value value') :
    EnvRel n ⟨[(ofString "f", value)]⟩ ⟨[(ofString "f", value')]⟩ := by
  apply (envRel_iff_lookup _ _ _).2
  apply aLookupRel_cons
  · intro _
    exact related
  · exact aLookupRel_empty _ _

/-- Forcing preserves the forward simulation, using the induction hypotheses
for the arguments and the smaller generated application. -/
theorem compile_force_simulation_at_clock {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (args : List FlatLang.Exp) (clock : Nat)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression)
    (bodyIH : ∀ (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value)
      (source target sourceFinal : FlatSem.State C F) (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
      source.clock ≤ clock →
      FlatSem.evaluate sourceEnv source [FlatSem.appUnit (.varLocal .none (ofString "f"))] = (sourceFinal, sourceResult) →
      EnvRel n sourceEnv targetEnv → StateRel stateCfg source target →
      (compileExp cfg (FlatSem.appUnit (.varLocal .none (ofString "f")))).1 < n →
      sourceResult ≠ .err (.abort .typeError) →
      ∃ targetFinal targetResult,
        FlatSem.evaluate targetEnv target [(compileExp cfg (FlatSem.appUnit (.varLocal .none (ofString "f")))).2.2] =
          (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult) :
    ∀ (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (source target sourceFinal : FlatSem.State C F)
      (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
      source.clock = clock →
      FlatSem.evaluate sourceEnv source [.app trace (.src (.thunkOp .forceThunk)) args] = (sourceFinal, sourceResult) →
      EnvRel n sourceEnv targetEnv → StateRel stateCfg source target →
      (compileExp cfg (.app trace (.src (.thunkOp .forceThunk)) args)).1 < n →
      sourceResult ≠ .err (.abort .typeError) →
      ∃ targetFinal targetResult,
        FlatSem.evaluate targetEnv target [(compileExp cfg (.app trace (.src (.thunkOp .forceThunk)) args)).2.2] =
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
      have outer := evaluate_app_args_error sourceEnv source sourceNext trace (.src (.thunkOp .forceThunk)) args (.abort .typeError) argsRun
      rw [sourceEval] at outer
      exact safe (congrArg Prod.snd outer)
    obtain ⟨targetNext, targetArgsResult, targetArgsRun, nextStates, related⟩ := argsSim
      sourceEnv targetEnv source target sourceNext argsResult n argsRun envs states reversedBound argsSafe
    cases related with
    | error errorsRel =>
      rename_i leftError rightError
      have sourceOuter := evaluate_app_args_error sourceEnv source sourceNext trace (.src (.thunkOp .forceThunk)) args leftError argsRun
      have targetOuter := evaluate_app_args_error targetEnv target targetNext trace (.src (.thunkOp .forceThunk))
        (compileExps cfg args).2.2 rightError (by simpa [compiledReverse] using targetArgsRun)
      have equal := sourceEval.symm.trans sourceOuter
      cases equal
      exact ⟨_, _, by simpa [compileExp_app] using targetOuter,
        stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, .error errorsRel⟩
    | values valuesRel =>
      rename_i sourceValues targetValues
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
            refine ⟨targetFixed, .val [targetValue], ?_, fixedStates, .values (.cons valueRelated .nil)⟩
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
                simpa [sourceFixed, clockEq] using Nat.min_le_left source.clock sourceNext.clock
              obtain ⟨targetLast, targetResult, targetBodyRun, lastStates, resultRel⟩ := bodyIH
                bodyEnv bodyEnv' sourceFixed targetFixed sourceLast bodyResult m clockBound bodyRun
                (forceBody_envRel m value targetValue valueRelated) fixedStates (by simp [m, body]) bodySafe
              have targetBody : FlatSem.evaluate bodyEnv' targetFixed [body] = (targetLast, targetResult) := by
                simpa [body, compile_forceBody] using targetBodyRun
              have targetBody' : FlatSem.evaluate ⟨[(ofString "f", targetValue)]⟩
                  { targetNext with clock := min target.clock targetNext.clock }
                  [FlatSem.appUnit (.varLocal .none (ofString "f"))] = (targetLast, targetResult) := targetBody
              cases resultRel with
              | error errors =>
                rename_i leftError rightError
                simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, sourceFixed, thunk, bodyRun'] at sourceEval
                rcases sourceEval with ⟨rfl, rfl⟩
                refine ⟨targetLast, .err rightError, ?_, lastStates, .error errors⟩
                simp [compileExp_app, FlatSem.evaluate, targetArgsRun', FlatSem.fixClock,
                  targetFixed, targetThunk, targetBody']
              | values results =>
                rename_i leftValues rightValues
                cases updated : FlatSem.updateThunk sourceValues sourceLast.refs leftValues with
                | none =>
                  simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, sourceFixed, thunk, bodyRun', updated] at sourceEval
                  exact (safe sourceEval.2.symm).elim
                | some refs =>
                  obtain ⟨refs', updated', refsRel⟩ := updateThunk_related valuesRel results lastStates.2.1 updated
                  simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, sourceFixed, thunk, bodyRun', updated] at sourceEval
                  rcases sourceEval with ⟨rfl, rfl⟩
                  refine ⟨{ targetLast with refs := refs' }, .val rightValues, ?_, ?_, .values results⟩
                  · simp [compileExp_app, FlatSem.evaluate, targetArgsRun', FlatSem.fixClock,
                      targetFixed, targetThunk, targetBody', updated']
                  · exact ⟨lastStates.1, refsRel, lastStates.2.2⟩

end Flapjack.Compiler.Backend.FlatPattern
