import Flapjack.Compiler.Backend.FlatPattern.Proofs.ClockedExpressionList
import Flapjack.Compiler.Backend.FlatPattern.Proofs.SourceApplication
import Flapjack.Compiler.Backend.FlatPattern.Proofs.ThunkEvaluation
import Flapjack.Compiler.Backend.FlatPattern.Proofs.DynamicEvaluation

/-! Clock-bounded application simulation for the proof-side flat pattern pass.
The evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)
open Flapjack.Basis.Pure.MlString (ofString)

/-- Nonrecursive source applications simulate their arguments and then use
the primitive-operation correspondence proved for their operator. -/
theorem compile_simpleSourceApp_simulation_upTo {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (op : Op) (args : List FlatLang.Exp) (clock : Nat)
    (notCall : op ≠ .opapp) (notEval : op ≠ .eval) (notForce : op ≠ .thunkOp .forceThunk)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression)
    (primitiveRel : ∀ (source target sourceFinal : FlatSem.State C F) (values values' : List FlatSem.Value)
      (result : Result FlatSem.Value FlatSem.Value), StateRel stateCfg source target → List.Forall₂ ValueRel values values' →
      FlatSem.doApp source (.src op) values = some (sourceFinal, result) →
      ∃ targetFinal result', FlatSem.doApp target (.src op) values' = some (targetFinal, result') ∧
        StateRel stateCfg sourceFinal targetFinal ∧ PrimitiveResultRel result result') :
    ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock (.app trace (.src op) args) := by
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
      have outer := evaluate_app_args_error sourceEnv source sourceNext trace (.src op) args (.abort .typeError) argsRun
      rw [sourceEval] at outer
      exact safe (congrArg Prod.snd outer)
    obtain ⟨targetNext, targetArgsResult, targetArgsRun, nextStates, related⟩ := argsSim
      sourceEnv targetEnv source target sourceNext argsResult n clockBound argsRun envs states reversedBound argsSafe
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


/-- Arithmetic, conversion, shift, typed comparison, references, arrays,
 list, vector and string operations, FFI and explicit thunk applications simulate
their compiled expressions using only argument induction hypotheses. -/
theorem compile_coveredSourceApp_simulation_upTo {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (op : Op) (args : List FlatLang.Exp) (clock : Nat) (covered : CoveredSourcePrimitive op)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression) :
    ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock (.app trace (.src op) args) := by
  have notCall : op ≠ .opapp := by
    cases covered <;> simp
    case aupdate unsafeOp => cases unsafeOp <;> simp
    case asub unsafeOp => cases unsafeOp <;> simp
    case aw8sub unsafeOp => cases unsafeOp <;> simp
    case aw8update unsafeOp => cases unsafeOp <;> simp
    case vsub unsafeOp => cases unsafeOp <;> simp
  have notEval : op ≠ .eval := by
    cases covered <;> simp
    case aupdate unsafeOp => cases unsafeOp <;> simp
    case asub unsafeOp => cases unsafeOp <;> simp
    case aw8sub unsafeOp => cases unsafeOp <;> simp
    case aw8update unsafeOp => cases unsafeOp <;> simp
    case vsub unsafeOp => cases unsafeOp <;> simp
  have notForce : op ≠ .thunkOp .forceThunk := by
    cases covered <;> simp
    case aupdate unsafeOp => cases unsafeOp <;> simp
    case asub unsafeOp => cases unsafeOp <;> simp
    case aw8sub unsafeOp => cases unsafeOp <;> simp
    case aw8update unsafeOp => cases unsafeOp <;> simp
    case vsub unsafeOp => cases unsafeOp <;> simp
  apply compile_simpleSourceApp_simulation_upTo cfg stateCfg trace op args clock notCall notEval notForce argumentsIH
  intro source target sourceFinal values values' result states related run
  cases covered with
  | arith action typ => exact doApp_arith_related stateCfg source target sourceFinal action typ values values' result states related run
  | fromTo sourceTyp targetTyp => exact doApp_fromTo_related stateCfg source target sourceFinal sourceTyp targetTyp values values' result states related run
  | shift width shift amount => exact doApp_shift_related stateCfg source target sourceFinal width shift amount values values' result states related run
  | test test typ => exact doApp_test_related stateCfg source target sourceFinal test typ values values' result states related run
  | equality => exact doApp_equality_related stateCfg source target sourceFinal values values' result states related run
  | opref => exact doApp_refAlloc_complete stateCfg source target sourceFinal values values' result states related run
  | opassign => exact doApp_refAssign_complete stateCfg source target sourceFinal values values' result states related run
  | opderef => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  | aallocEmpty => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  | envId => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  | aallocFixed => exact doApp_arrayFixed_complete stateCfg source target sourceFinal values values' result states related run
  | aalloc => exact doApp_arrayAlloc_complete stateCfg source target sourceFinal values values' result states related run
  | aw8alloc => exact doApp_byteArrayAlloc_complete stateCfg source target sourceFinal values values' result states related run
  | alength => exact doApp_arrayLength_complete stateCfg source target sourceFinal values values' result states related run
  | aw8length => exact doApp_byteArrayLength_complete stateCfg source target sourceFinal values values' result states related run
  | aupdate unsafeOp => exact doApp_arrayUpdate_complete stateCfg source target sourceFinal unsafeOp values values' result states related run
  | asub unsafeOp => exact doApp_arrayRead_complete stateCfg source target sourceFinal unsafeOp values values' result states related run
  | aw8sub unsafeOp => exact doApp_byteArrayRead_complete stateCfg source target sourceFinal unsafeOp values values' result states related run
  | aw8update unsafeOp => exact doApp_byteArrayUpdate_complete stateCfg source target sourceFinal unsafeOp values values' result states related run
  | vfromList => exact doApp_vectorFromList_related stateCfg source target sourceFinal values values' result states related run
  | vlength => exact doApp_vectorLength_related stateCfg source target sourceFinal values values' result states related run
  | listAppend => exact doApp_listAppend_related stateCfg source target sourceFinal values values' result states related run
  | strlen => exact doApp_stringLength_related stateCfg source target sourceFinal values values' result states related run
  | explode => exact doApp_stringExplode_related stateCfg source target sourceFinal values values' result states related run
  | implode => exact doApp_stringImplode_related stateCfg source target sourceFinal values values' result states related run
  | strsub => exact doApp_stringSub_related stateCfg source target sourceFinal values values' result states related run
  | strcat => exact doApp_stringConcat_related stateCfg source target sourceFinal values values' result states related run
  | configGC => exact doApp_configGC_related stateCfg source target sourceFinal values values' result states related run
  | copyStrStr => exact doApp_copyStrStr_related stateCfg source target sourceFinal values values' result states related run
  | copyAw8Str => exact doApp_copyAw8Str_related stateCfg source target sourceFinal values values' result states related run
  | copyStrAw8 => exact doApp_copyStrAw8_related stateCfg source target sourceFinal values values' result states related run
  | copyAw8Aw8 => exact doApp_copyAw8Aw8_related stateCfg source target sourceFinal values values' result states related run
  | xorAw8StrUnsafe => exact doApp_xorAw8Str_related stateCfg source target sourceFinal values values' result states related run
  | vsub unsafeOp => exact doApp_vectorRead_related stateCfg source target sourceFinal unsafeOp values values' result states related run
  | ffi name => exact doApp_ffi_related stateCfg source target sourceFinal name values values' result states related run
  | allocThunk mode => exact doApp_thunkAlloc_related stateCfg source target sourceFinal mode values values' result states related run
  | updateThunk mode => exact doApp_thunkUpdate_related stateCfg source target sourceFinal mode values values' result states related run


/-- Every flat-specific primitive application simulates its compiled form,
assuming the usual induction hypotheses for its argument expressions. -/
theorem compile_flatApp_simulation_upTo {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (op : FlatLang.Op) (args : List FlatLang.Exp) (clock : Nat) (notSource : ∀ sourceOp, op ≠ .src sourceOp)
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

/-- Every nonrecursive source application simulates up to the same clock
bound, assuming its arguments do. -/
theorem compile_nonrecursiveSourceApp_simulation_upTo {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (op : Op) (args : List FlatLang.Exp) (clock : Nat) (notCall : op ≠ .opapp)
    (notEval : op ≠ .eval) (notForce : op ≠ .thunkOp .forceThunk)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression) :
    ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock (.app trace (.src op) args) :=
  compile_coveredSourceApp_simulation_upTo cfg stateCfg trace op args clock
    (covered_simpleSourcePrimitive op notCall notEval notForce) argumentsIH

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
        (targetFinal, targetOutcome) ∧ StateRel stateCfg sourceFinal targetFinal ∧ optionRel FlatErrorRel outcome targetOutcome) :
    ∀ (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (source target sourceFinal : FlatSem.State C F)
      (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
      source.clock = clock →
      FlatSem.evaluate sourceEnv source [.app trace (.src .eval) args] = (sourceFinal, sourceResult) →
      EnvRel n sourceEnv targetEnv → StateRel stateCfg source target →
      (compileExp cfg (.app trace (.src .eval) args)).1 < n →
      sourceResult ≠ .err (.abort .typeError) →
      ∃ targetFinal targetResult,
        FlatSem.evaluate targetEnv target [(compileExp cfg (.app trace (.src .eval) args)).2.2] =
          (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult := by
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
    cases related with
    | error errorsRel =>
      rename_i leftError rightError
      have sourceOuter := evaluate_app_args_error sourceEnv source sourceNext trace (.src .eval) args leftError argsRun
      have targetOuter := evaluate_app_args_error targetEnv target targetNext trace (.src .eval)
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
      cases decoded : FlatSem.doEval sourceValues.reverse sourceNext.evalConfig with
      | none =>
        have bad := evaluate_eval_bad sourceEnv source sourceNext trace args sourceValues argsRun decoded
        rw [sourceEval] at bad
        exact (safe (congrArg Prod.snd bad)).elim
      | some payload =>
        obtain ⟨declarations, sourceConfig, result⟩ := payload
        obtain ⟨targetConfig, targetValue, targetDecoded, installedStates, valueRel⟩ :=
          doEval_state_simulation stateCfg sourceFixed targetFixed sourceValues.reverse targetValues.reverse fixedStates
            (valueRel_reverse valuesRel) declarations sourceConfig result decoded
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
          exact ⟨_, _, by simpa [compileExp_app] using targetOuter, installedStates, .error (.abort .timeoutError)⟩
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
                exact ⟨targetLast, _, by simpa [compileExp_app] using targetOuter, finalRel, .values (.cons valueRel .nil)⟩
            | some error =>
              cases targetOutcome with
              | none => simp [optionRel] at outcomeRel
              | some targetError =>
                have errorsRel : FlatErrorRel error targetError := by simpa [optionRel] using outcomeRel
                have sourceOuter := evaluate_eval_declarations sourceEnv source sourceNext sourceLast trace args sourceValues
                  declarations sourceConfig result (some error) argsRun decoded zero declsRun
                have targetOuter := evaluate_eval_declarations targetEnv target targetNext targetLast trace (compileExps cfg args).2.2
                  targetValues (declarations.map (compileDec stateCfg)) targetConfig targetValue (some targetError)
                  (by simpa [compiledReverse] using targetArgsRun) targetDecoded targetNonzero targetDeclsRun
                have equal := sourceEval.symm.trans sourceOuter
                cases equal
                exact ⟨targetLast, _, by simpa [compileExp_app] using targetOuter, finalRel, .error errorsRel⟩

end Flapjack.Compiler.Backend.FlatPattern
