import Flapjack.Compiler.Backend.FlatPattern.Proofs.FlatApplication
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveComparison
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveThunk
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveAccess

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

/-- Reference allocation preserves arbitrary successful primitive results. -/
theorem doApp_refAlloc_complete {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .opref) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .opref) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases result with
  | val value =>
    obtain ⟨targetFinal, value', targetRun, finalStates, valueRel⟩ :=
      doApp_refAlloc_related cfg source target values values' states related sourceFinal value run
    exact ⟨targetFinal, .val value', targetRun, finalStates, .value valueRel⟩
  | err error =>
    cases values with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | cons value tail =>
      cases tail <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
        Flapjack.SemanticPrimitivesHOL.storeAlloc] at run

/-- Reference assignment preserves arbitrary successful primitive results. -/
theorem doApp_refAssign_complete {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .opassign) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .opassign) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases result with
  | val value =>
    obtain ⟨targetFinal, value', targetRun, finalStates, valueRel⟩ :=
      doApp_refAssign_related cfg source target values values' states related sourceFinal value run
    exact ⟨targetFinal, .val value', targetRun, finalStates, .value valueRel⟩
  | err error =>
    cases values with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | cons value tail =>
      cases tail with
      | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
      | cons second rest =>
        cases rest with
        | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
        | nil =>
          cases value with
          | loc flag address =>
            cases assigned : Flapjack.SemanticPrimitivesHOL.storeAssign address (.refv second) source.refs <;>
              simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, assigned] at run
          | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
            simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run

/-- Fixed-array allocation preserves arbitrary successful primitive results. -/
theorem doApp_arrayFixed_complete {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .aallocFixed) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .aallocFixed) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  obtain ⟨sourceAfter, targetAfter, value, sourceRun, targetRun, finalStates, valueRel⟩ :=
    doApp_arrayFixed_related cfg source target values values' states related
  have equal := sourceRun.symm.trans run
  cases equal
  exact ⟨targetAfter, .val value, targetRun, finalStates, .value valueRel⟩

/-- Value-array allocation preserves arbitrary successful primitive results. -/
theorem doApp_arrayAlloc_complete {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .aalloc) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .aalloc) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
  | @cons size size' tail tail' sizeRel rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | @cons value value' tail tail' valueRel rest =>
      cases rest with
      | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
      | nil =>
        cases size with
        | litv literal =>
          have eq := (valueRel_lit literal size').1 sizeRel
          subst size'
          cases literal with
          | intLit size =>
            obtain ⟨sourceAfter, targetAfter, result, result', sourceRun, targetRun, finalStates, resultRel⟩ :=
              doApp_arrayAlloc_related cfg source target size value value' states valueRel
            have equal := sourceRun.symm.trans run
            cases equal
            exact ⟨targetAfter, result', targetRun, finalStates, resultRel⟩
          | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
            simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
        | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run

/-- Byte-array allocation preserves arbitrary successful primitive results. -/
theorem doApp_byteArrayAlloc_complete {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .aw8alloc) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .aw8alloc) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
  | @cons size size' tail tail' sizeRel rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | @cons value value' tail tail' valueRel rest =>
      cases rest with
      | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
      | nil =>
        cases size with
        | litv literal =>
          have eq := (valueRel_lit literal size').1 sizeRel
          subst size'
          cases literal with
          | intLit size =>
            cases value with
            | litv literal =>
              have eq := (valueRel_lit literal value').1 valueRel
              subst value'
              cases literal with
              | word8 byte =>
                obtain ⟨sourceAfter, targetAfter, result, sourceRun, targetRun, finalStates, resultRel⟩ :=
                  doApp_byteArrayAlloc_related cfg source target size byte states
                have equal := sourceRun.symm.trans run
                cases equal
                exact ⟨targetAfter, result, targetRun, finalStates, resultRel⟩
              | intLit _ | word64 _ | char _ | strLit _ | float64 _ =>
                simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
            | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
              simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
          | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
            simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
        | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run

/-- Source operators whose primitive relation has been established here. -/
inductive CoveredSourcePrimitive : Op → Prop where
  | arith (action : Arith) (typ : PrimType) : CoveredSourcePrimitive (.arith action typ)
  | fromTo (source target : PrimType) : CoveredSourcePrimitive (.fromTo source target)
  | shift (width : WordSize) (shift : Shift) (amount : Nat) : CoveredSourcePrimitive (.shift width shift amount)
  | test (test : Test) (typ : PrimType) : CoveredSourcePrimitive (.test test typ)
  | opref : CoveredSourcePrimitive .opref
  | opassign : CoveredSourcePrimitive .opassign
  | aallocFixed : CoveredSourcePrimitive .aallocFixed
  | aalloc : CoveredSourcePrimitive .aalloc
  | aw8alloc : CoveredSourcePrimitive .aw8alloc
  | alength : CoveredSourcePrimitive .alength
  | aw8length : CoveredSourcePrimitive .aw8length
  | aupdate (unsafeOp : Bool) : CoveredSourcePrimitive (if unsafeOp then .aupdateUnsafe else .aupdate)
  | asub (unsafeOp : Bool) : CoveredSourcePrimitive (if unsafeOp then .asubUnsafe else .asub)
  | ffi (name : Flapjack.Basis.Pure.MlString.MlString) : CoveredSourcePrimitive (.ffi name)
  | allocThunk (mode : ThunkMode) : CoveredSourcePrimitive (.thunkOp (.allocThunk mode))
  | updateThunk (mode : ThunkMode) : CoveredSourcePrimitive (.thunkOp (.updateThunk mode))

/-- Arithmetic, conversion, shift, typed comparison, references, array
allocation, FFI and explicit thunk applications simulate their compiled
expressions using only argument induction hypotheses. -/
theorem compile_coveredSourceApp_simulation {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (op : Op) (args : List FlatLang.Exp) (covered : CoveredSourcePrimitive op)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.app trace (.src op) args) := by
  have notCall : op ≠ .opapp := by
    cases covered <;> simp
    case aupdate unsafeOp => cases unsafeOp <;> simp
    case asub unsafeOp => cases unsafeOp <;> simp
  have notEval : op ≠ .eval := by
    cases covered <;> simp
    case aupdate unsafeOp => cases unsafeOp <;> simp
    case asub unsafeOp => cases unsafeOp <;> simp
  have notForce : op ≠ .thunkOp .forceThunk := by
    cases covered <;> simp
    case aupdate unsafeOp => cases unsafeOp <;> simp
    case asub unsafeOp => cases unsafeOp <;> simp
  apply compile_simpleSourceApp_simulation cfg stateCfg trace op args notCall notEval notForce argumentsIH
  intro source target sourceFinal values values' result states related run
  cases covered with
  | arith action typ => exact doApp_arith_related stateCfg source target sourceFinal action typ values values' result states related run
  | fromTo sourceTyp targetTyp => exact doApp_fromTo_related stateCfg source target sourceFinal sourceTyp targetTyp values values' result states related run
  | shift width shift amount => exact doApp_shift_related stateCfg source target sourceFinal width shift amount values values' result states related run
  | test test typ => exact doApp_test_related stateCfg source target sourceFinal test typ values values' result states related run
  | opref => exact doApp_refAlloc_complete stateCfg source target sourceFinal values values' result states related run
  | opassign => exact doApp_refAssign_complete stateCfg source target sourceFinal values values' result states related run
  | aallocFixed => exact doApp_arrayFixed_complete stateCfg source target sourceFinal values values' result states related run
  | aalloc => exact doApp_arrayAlloc_complete stateCfg source target sourceFinal values values' result states related run
  | aw8alloc => exact doApp_byteArrayAlloc_complete stateCfg source target sourceFinal values values' result states related run
  | alength => exact doApp_arrayLength_complete stateCfg source target sourceFinal values values' result states related run
  | aw8length => exact doApp_byteArrayLength_complete stateCfg source target sourceFinal values values' result states related run
  | aupdate unsafeOp => exact doApp_arrayUpdate_complete stateCfg source target sourceFinal unsafeOp values values' result states related run
  | asub unsafeOp => exact doApp_arrayRead_complete stateCfg source target sourceFinal unsafeOp values values' result states related run
  | ffi name => exact doApp_ffi_related stateCfg source target sourceFinal name values values' result states related run
  | allocThunk mode => exact doApp_thunkAlloc_related stateCfg source target sourceFinal mode values values' result states related run
  | updateThunk mode => exact doApp_thunkUpdate_related stateCfg source target sourceFinal mode values values' result states related run
end Flapjack.Compiler.Backend.FlatPattern
