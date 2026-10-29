import Flapjack.Compiler.Backend.FlatPattern.Proofs.FlatApplication
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveComparison
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveThunk

/-! Source-primitive applications in the proof-side pattern simulation. The
evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Nonrecursive source applications dispatch their evaluated arguments to
the primitive evaluator after clamping the clock. -/
theorem evaluate_simpleSourceApp_values {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (op : Op)
    (args : List FlatLang.Exp) (values : List FlatSem.Value)
    (notCall : op ≠ .opapp) (notEval : op ≠ .eval) (notForce : op ≠ .thunkOp .forceThunk)
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .val values)) :
    FlatSem.evaluate env state [.app trace (.src op) args] =
      FlatSem.applyResult { next with clock := min state.clock next.clock } (.src op) values.reverse := by
  cases op <;> simp_all [FlatSem.evaluate, FlatSem.fixClock]

/-- Nonrecursive source applications simulate their arguments and then use
the primitive-operation correspondence proved for their operator. -/
theorem compile_simpleSourceApp_simulation {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (op : Op) (args : List FlatLang.Exp)
    (notCall : op ≠ .opapp) (notEval : op ≠ .eval) (notForce : op ≠ .thunkOp .forceThunk)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression)
    (primitiveRel : ∀ (source target sourceFinal : FlatSem.State C F) (values values' : List FlatSem.Value)
      (result : Result FlatSem.Value FlatSem.Value), StateRel stateCfg source target → List.Forall₂ ValueRel values values' →
      FlatSem.doApp source (.src op) values = some (sourceFinal, result) →
      ∃ targetFinal result', FlatSem.doApp target (.src op) values' = some (targetFinal, result') ∧
        StateRel stateCfg sourceFinal targetFinal ∧ PrimitiveResultRel result result') :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.app trace (.src op) args) := by
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
      have outer := evaluate_app_args_error sourceEnv source sourceNext trace (.src op) args (.abort .typeError) argsRun
      rw [sourceEval] at outer
      exact safe (congrArg Prod.snd outer)
    obtain ⟨targetNext, targetArgsResult, targetArgsRun, nextStates, related⟩ := argsSim
      sourceEnv targetEnv source target sourceNext argsResult n argsRun envs states reversedBound argsSafe
    cases related with
    | error errorsRel =>
      rename_i leftError rightError
      have sourceOuter := evaluate_app_args_error sourceEnv source sourceNext trace (.src op) args leftError argsRun
      have targetOuter := evaluate_app_args_error targetEnv target targetNext trace (.src op)
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
      have sourceOuter := evaluate_simpleSourceApp_values sourceEnv source sourceNext trace op args sourceValues notCall notEval notForce argsRun
      have targetOuter := evaluate_simpleSourceApp_values targetEnv target targetNext trace op (compileExps cfg args).2.2
        targetValues notCall notEval notForce (by simpa [compiledReverse] using targetArgsRun)
      cases primitive : FlatSem.doApp sourceFixed (.src op) sourceValues.reverse with
      | none =>
        have bad : sourceResult = .err (.abort .typeError) := by
          have eq := sourceOuter.symm.trans sourceEval
          simpa [FlatSem.applyResult, sourceFixed, primitive] using (congrArg Prod.snd eq).symm
        exact (safe bad).elim
      | some outcome =>
        obtain ⟨sourceAfter, result⟩ := outcome
        obtain ⟨targetAfter, result', targetPrimitive, afterStates, resultRel⟩ := primitiveRel sourceFixed targetFixed sourceAfter sourceValues.reverse targetValues.reverse result
          fixedStates (valueRel_reverse valuesRel) primitive
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

/-- Source operators whose primitive relation has been established here. -/
inductive CoveredSourcePrimitive : Op → Prop where
  | arith (action : Arith) (typ : PrimType) : CoveredSourcePrimitive (.arith action typ)
  | fromTo (source target : PrimType) : CoveredSourcePrimitive (.fromTo source target)
  | shift (width : WordSize) (shift : Shift) (amount : Nat) : CoveredSourcePrimitive (.shift width shift amount)
  | test (test : Test) (typ : PrimType) : CoveredSourcePrimitive (.test test typ)
  | ffi (name : Flapjack.Basis.Pure.MlString.MlString) : CoveredSourcePrimitive (.ffi name)
  | allocThunk (mode : ThunkMode) : CoveredSourcePrimitive (.thunkOp (.allocThunk mode))
  | updateThunk (mode : ThunkMode) : CoveredSourcePrimitive (.thunkOp (.updateThunk mode))

/-- Arithmetic, conversion, shift, typed comparison, FFI and explicit thunk
applications simulate their compiled expressions using only argument
induction hypotheses. -/
theorem compile_coveredSourceApp_simulation {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (op : Op) (args : List FlatLang.Exp) (covered : CoveredSourcePrimitive op)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.app trace (.src op) args) := by
  have notCall : op ≠ .opapp := by cases covered <;> simp
  have notEval : op ≠ .eval := by cases covered <;> simp
  have notForce : op ≠ .thunkOp .forceThunk := by cases covered <;> simp
  apply compile_simpleSourceApp_simulation cfg stateCfg trace op args notCall notEval notForce argumentsIH
  intro source target sourceFinal values values' result states related run
  cases covered with
  | arith action typ => exact doApp_arith_related stateCfg source target sourceFinal action typ values values' result states related run
  | fromTo sourceTyp targetTyp => exact doApp_fromTo_related stateCfg source target sourceFinal sourceTyp targetTyp values values' result states related run
  | shift width shift amount => exact doApp_shift_related stateCfg source target sourceFinal width shift amount values values' result states related run
  | test test typ => exact doApp_test_related stateCfg source target sourceFinal test typ values values' result states related run
  | ffi name => exact doApp_ffi_related stateCfg source target sourceFinal name values values' result states related run
  | allocThunk mode => exact doApp_thunkAlloc_related stateCfg source target sourceFinal mode values values' result states related run
  | updateThunk mode => exact doApp_thunkUpdate_related stateCfg source target sourceFinal mode values values' result states related run
end Flapjack.Compiler.Backend.FlatPattern
