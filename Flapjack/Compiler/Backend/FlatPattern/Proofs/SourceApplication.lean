import Flapjack.Compiler.Backend.FlatPattern.Proofs.FunctionApplication
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveGlobals
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveComparison
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveThunk
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveAccess
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveVector
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveString
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveCopy
import Flapjack.Compiler.Backend.FlatPattern.Proofs.StructuralEquality

/-! Source-primitive applications in the proof-side pattern simulation. The
evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Flapjack evaluation infrastructure for nonrecursive applications: the
evaluated arguments are dispatched to the primitive evaluator. -/
theorem evaluate_simpleApp_values {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (op : FlatLang.Op)
    (args : List FlatLang.Exp) (values : List FlatSem.Value)
    (notCall : op ≠ .src .opapp) (notEval : op ≠ .src .eval)
    (notForce : op ≠ .src (.thunkOp .forceThunk))
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .val values)) :
    FlatSem.evaluate env state [.app trace op args] =
      FlatSem.applyResult { next with clock := min state.clock next.clock } op values.reverse := by
  cases op with
  | src sourceOp => cases sourceOp <;> simp_all [FlatSem.evaluate, FlatSem.fixClock]
  | globalVarAlloc _ | globalVarInit _ | globalVarLookup _ | tagLenEq _ _ | lenEq _ | el _ | id =>
    simp [FlatSem.evaluate, FlatSem.fixClock, argsRun]

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

/-- Flapjack intermediate for source operators in `do_app_thm`; HOL derives
the full theorem from `simple_do_app_thm`. -/
theorem doApp_source_related {C F : Type} (cfg : Config) (op : Op)
    (source target sourceFinal : FlatSem.State C F) (values values' : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (states : StateRel cfg source target)
    (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src op) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src op) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases op with
  | arith action typ => exact doApp_arith_related cfg source target sourceFinal action typ values values' result states related run
  | fromTo sourceTyp targetTyp => exact doApp_fromTo_related cfg source target sourceFinal sourceTyp targetTyp values values' result states related run
  | shift width shift amount => exact doApp_shift_related cfg source target sourceFinal width shift amount values values' result states related run
  | test test typ => exact doApp_test_related cfg source target sourceFinal test typ values values' result states related run
  | equality => exact doApp_equality_related cfg source target sourceFinal values values' result states related run
  | opref => exact doApp_refAlloc_complete cfg source target sourceFinal values values' result states related run
  | opassign => exact doApp_refAssign_complete cfg source target sourceFinal values values' result states related run
  | opderef => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  | aallocEmpty => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  | envId => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  | aallocFixed => exact doApp_arrayFixed_complete cfg source target sourceFinal values values' result states related run
  | aalloc => exact doApp_arrayAlloc_complete cfg source target sourceFinal values values' result states related run
  | aw8alloc => exact doApp_byteArrayAlloc_complete cfg source target sourceFinal values values' result states related run
  | alength => exact doApp_arrayLength_complete cfg source target sourceFinal values values' result states related run
  | aw8length => exact doApp_byteArrayLength_complete cfg source target sourceFinal values values' result states related run
  | aupdate => exact doApp_arrayUpdate_complete cfg source target sourceFinal false values values' result states related run
  | aupdateUnsafe => exact doApp_arrayUpdate_complete cfg source target sourceFinal true values values' result states related run
  | asub => exact doApp_arrayRead_complete cfg source target sourceFinal false values values' result states related run
  | asubUnsafe => exact doApp_arrayRead_complete cfg source target sourceFinal true values values' result states related run
  | aw8sub => exact doApp_byteArrayRead_complete cfg source target sourceFinal false values values' result states related run
  | aw8subUnsafe => exact doApp_byteArrayRead_complete cfg source target sourceFinal true values values' result states related run
  | aw8update => exact doApp_byteArrayUpdate_complete cfg source target sourceFinal false values values' result states related run
  | aw8updateUnsafe => exact doApp_byteArrayUpdate_complete cfg source target sourceFinal true values values' result states related run
  | vfromList => exact doApp_vectorFromList_related cfg source target sourceFinal values values' result states related run
  | vlength => exact doApp_vectorLength_related cfg source target sourceFinal values values' result states related run
  | listAppend => exact doApp_listAppend_related cfg source target sourceFinal values values' result states related run
  | strlen => exact doApp_stringLength_related cfg source target sourceFinal values values' result states related run
  | explode => exact doApp_stringExplode_related cfg source target sourceFinal values values' result states related run
  | implode => exact doApp_stringImplode_related cfg source target sourceFinal values values' result states related run
  | strsub => exact doApp_stringSub_related cfg source target sourceFinal values values' result states related run
  | strcat => exact doApp_stringConcat_related cfg source target sourceFinal values values' result states related run
  | configGC => exact doApp_configGC_related cfg source target sourceFinal values values' result states related run
  | copyStrStr => exact doApp_copyStrStr_related cfg source target sourceFinal values values' result states related run
  | copyAw8Str => exact doApp_copyAw8Str_related cfg source target sourceFinal values values' result states related run
  | copyStrAw8 => exact doApp_copyStrAw8_related cfg source target sourceFinal values values' result states related run
  | copyAw8Aw8 => exact doApp_copyAw8Aw8_related cfg source target sourceFinal values values' result states related run
  | xorAw8StrUnsafe => exact doApp_xorAw8Str_related cfg source target sourceFinal values values' result states related run
  | vsub => exact doApp_vectorRead_related cfg source target sourceFinal false values values' result states related run
  | vsubUnsafe => exact doApp_vectorRead_related cfg source target sourceFinal true values values' result states related run
  | ffi name => exact doApp_ffi_related cfg source target sourceFinal name values values' result states related run
  | opapp | eval => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  | thunkOp thunk =>
    cases thunk with
    | allocThunk mode => exact doApp_thunkAlloc_related cfg source target sourceFinal mode values values' result states related run
    | updateThunk mode => exact doApp_thunkUpdate_related cfg source target sourceFinal mode values values' result states related run
    | forceThunk => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run

@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "do_app_thm"]
theorem doApp_simulation {C F : Type} (source : FlatSem.State C F) (values : List FlatSem.Value)
    (sourceFinal : FlatSem.State C F) (result : Result FlatSem.Value FlatSem.Value)
    (target : FlatSem.State C F) (values' : List FlatSem.Value) (op : FlatLang.Op) (cfg : Config)
    (run : FlatSem.doApp source op values = some (sourceFinal, result))
    (premises : StateRel cfg source target ∧ List.Forall₂ ValueRel values values') :
    ∃ targetFinal result', SemanticPrimitivesProps.resultRel ValueRel ValueRel result result' ∧
      StateRel cfg sourceFinal targetFinal ∧ FlatSem.doApp target op values' = some (targetFinal, result') := by
  have sim : ∃ targetFinal result', FlatSem.doApp target op values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
    by_cases isSource : ∃ sourceOp, op = .src sourceOp
    · obtain ⟨sourceOp, rfl⟩ := isSource
      exact doApp_source_related cfg sourceOp source target sourceFinal values values' result premises.1 premises.2 run
    · exact doApp_flat_related cfg source target sourceFinal op values values' result premises.1 premises.2
        (fun sourceOp eq => isSource ⟨sourceOp, eq⟩) run
  obtain ⟨targetFinal, result', targetRun, finalStates, related⟩ := sim
  refine ⟨targetFinal, result', ?_, finalStates, targetRun⟩
  cases related with
  | value values => exact values
  | error errors => exact errors

end Flapjack.Compiler.Backend.FlatPattern
