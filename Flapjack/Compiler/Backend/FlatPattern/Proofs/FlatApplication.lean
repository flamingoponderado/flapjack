import Flapjack.Compiler.Backend.FlatPattern.Proofs.FunctionApplication
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveGlobals

/-! Flat-primitive application in the proof-side pattern simulation. The
evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A flat-specific application dispatches its evaluated, reversed arguments
to the primitive evaluator after clamping the clock. -/
theorem evaluate_flatApp_values {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (op : FlatLang.Op)
    (args : List FlatLang.Exp) (values : List FlatSem.Value)
    (notSource : ∀ sourceOp, op ≠ .src sourceOp)
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .val values)) :
    FlatSem.evaluate env state [.app trace op args] =
      FlatSem.applyResult { next with clock := min state.clock next.clock } op values.reverse := by
  cases op with
  | src sourceOp => exact (notSource sourceOp rfl).elim
  | globalVarAlloc _ | globalVarInit _ | globalVarLookup _ | tagLenEq _ _ | lenEq _ | el _ | id =>
    simp [FlatSem.evaluate, FlatSem.fixClock, argsRun]

/-- Every flat-specific primitive application simulates its compiled form,
assuming the usual induction hypotheses for its argument expressions. -/
theorem compile_flatApp_simulation {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (op : FlatLang.Op) (args : List FlatLang.Exp) (notSource : ∀ sourceOp, op ≠ .src sourceOp)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.app trace op args) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states bound safe
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
      have outer := evaluate_app_args_error sourceEnv source sourceNext trace op args (.abort .typeError) argsRun
      rw [sourceEval] at outer
      exact safe (congrArg Prod.snd outer)
    obtain ⟨targetNext, targetArgsResult, targetArgsRun, nextStates, related⟩ := argsSim
      sourceEnv targetEnv source target sourceNext argsResult n argsRun envs states reversedBound argsSafe
    cases related with
    | error errorsRel =>
      rename_i leftError rightError
      have sourceOuter := evaluate_app_args_error sourceEnv source sourceNext trace op args leftError argsRun
      have targetOuter := evaluate_app_args_error targetEnv target targetNext trace op
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
      have sourceOuter := evaluate_flatApp_values sourceEnv source sourceNext trace op args sourceValues notSource argsRun
      have targetOuter := evaluate_flatApp_values targetEnv target targetNext trace op (compileExps cfg args).2.2
        targetValues notSource (by simpa [compiledReverse] using targetArgsRun)
      cases primitive : FlatSem.doApp sourceFixed op sourceValues.reverse with
      | none =>
        have bad : sourceResult = .err (.abort .typeError) := by
          have eq := sourceOuter.symm.trans sourceEval
          simpa [FlatSem.applyResult, sourceFixed, primitive] using (congrArg Prod.snd eq).symm
        exact (safe bad).elim
      | some outcome =>
        obtain ⟨sourceAfter, result⟩ := outcome
        obtain ⟨targetAfter, result', targetPrimitive, afterStates, resultRel⟩ := doApp_flat_related
          stateCfg sourceFixed targetFixed sourceAfter op sourceValues.reverse targetValues.reverse result
          fixedStates (valueRel_reverse valuesRel) notSource primitive
        cases resultRel with
        | value values =>
          have eq := sourceOuter.symm.trans sourceEval
          simp [FlatSem.applyResult, sourceFixed, primitive] at eq
          rcases eq with ⟨rfl, rfl⟩
          refine ⟨targetAfter, .val [_], ?_, afterStates, .values (.cons values .nil)⟩
          simpa [compileExp_app, FlatSem.applyResult, targetFixed, targetPrimitive] using targetOuter
        | error errors =>
          have eq := sourceOuter.symm.trans sourceEval
          simp [FlatSem.applyResult, sourceFixed, primitive] at eq
          rcases eq with ⟨rfl, rfl⟩
          refine ⟨targetAfter, .err _, ?_, afterStates, .error errors⟩
          simpa [compileExp_app, FlatSem.applyResult, targetFixed, targetPrimitive] using targetOuter

end Flapjack.Compiler.Backend.FlatPattern
