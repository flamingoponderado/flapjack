import Flapjack.Compiler.Backend.FlatPattern.Proofs.FlatApplication
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
  | equality : CoveredSourcePrimitive .equality
  | opref : CoveredSourcePrimitive .opref
  | opassign : CoveredSourcePrimitive .opassign
  | opderef : CoveredSourcePrimitive .opderef
  | aallocEmpty : CoveredSourcePrimitive .aallocEmpty
  | envId : CoveredSourcePrimitive .envId
  | aallocFixed : CoveredSourcePrimitive .aallocFixed
  | aalloc : CoveredSourcePrimitive .aalloc
  | aw8alloc : CoveredSourcePrimitive .aw8alloc
  | alength : CoveredSourcePrimitive .alength
  | aw8length : CoveredSourcePrimitive .aw8length
  | aupdate (unsafeOp : Bool) : CoveredSourcePrimitive (if unsafeOp then .aupdateUnsafe else .aupdate)
  | asub (unsafeOp : Bool) : CoveredSourcePrimitive (if unsafeOp then .asubUnsafe else .asub)
  | aw8sub (unsafeOp : Bool) : CoveredSourcePrimitive (if unsafeOp then .aw8subUnsafe else .aw8sub)
  | aw8update (unsafeOp : Bool) : CoveredSourcePrimitive (if unsafeOp then .aw8updateUnsafe else .aw8update)
  | vfromList : CoveredSourcePrimitive .vfromList
  | vlength : CoveredSourcePrimitive .vlength
  | listAppend : CoveredSourcePrimitive .listAppend
  | strlen : CoveredSourcePrimitive .strlen
  | explode : CoveredSourcePrimitive .explode
  | implode : CoveredSourcePrimitive .implode
  | strsub : CoveredSourcePrimitive .strsub
  | strcat : CoveredSourcePrimitive .strcat
  | configGC : CoveredSourcePrimitive .configGC
  | copyStrStr : CoveredSourcePrimitive .copyStrStr
  | copyAw8Str : CoveredSourcePrimitive .copyAw8Str
  | copyStrAw8 : CoveredSourcePrimitive .copyStrAw8
  | copyAw8Aw8 : CoveredSourcePrimitive .copyAw8Aw8
  | xorAw8StrUnsafe : CoveredSourcePrimitive .xorAw8StrUnsafe
  | vsub (unsafeOp : Bool) : CoveredSourcePrimitive (if unsafeOp then .vsubUnsafe else .vsub)
  | ffi (name : Flapjack.Basis.Pure.MlString.MlString) : CoveredSourcePrimitive (.ffi name)
  | allocThunk (mode : ThunkMode) : CoveredSourcePrimitive (.thunkOp (.allocThunk mode))
  | updateThunk (mode : ThunkMode) : CoveredSourcePrimitive (.thunkOp (.updateThunk mode))

/-- All source operations other than calls, dynamic evaluation, and forcing
are covered by the proof-side primitive simulation. Three operations are
covered because the current evaluator always rejects them; their fidelity to
the HOL evaluator remains part of the outstanding correspondence review. -/
theorem covered_simpleSourcePrimitive (op : Op) (notCall : op ≠ .opapp)
    (notEval : op ≠ .eval) (notForce : op ≠ .thunkOp .forceThunk) : CoveredSourcePrimitive op := by
  cases op <;> try contradiction
  all_goals first
    | exact .arith _ _
    | exact .fromTo _ _
    | exact .shift _ _ _
    | exact .equality
    | exact .test _ _
    | exact .opassign
    | exact .opref
    | exact .opderef
    | exact .aw8alloc
    | exact .aw8sub false
    | exact .aw8sub true
    | exact .aw8length
    | exact .aw8update false
    | exact .aw8update true
    | exact .copyStrStr
    | exact .copyStrAw8
    | exact .copyAw8Str
    | exact .copyAw8Aw8
    | exact .xorAw8StrUnsafe
    | exact .implode
    | exact .explode
    | exact .strsub
    | exact .strlen
    | exact .strcat
    | exact .vfromList
    | exact .vsub false
    | exact .vsub true
    | exact .vlength
    | exact .aalloc
    | exact .aallocEmpty
    | exact .aallocFixed
    | exact .asub false
    | exact .asub true
    | exact .alength
    | exact .aupdate false
    | exact .aupdate true
    | exact .listAppend
    | exact .configGC
    | exact .ffi _
    | exact .envId
    | (rename_i thunk; cases thunk with
      | allocThunk mode => exact .allocThunk mode
      | updateThunk mode => exact .updateThunk mode
      | forceThunk => exact (notForce rfl).elim)


/-- Flapjack dispatch infrastructure for the source cases of `do_app_thm`;
HOL instead derives that theorem from `simple_do_app_thm`. -/
theorem doApp_coveredSource_related {C F : Type} (cfg : Config) (op : Op)
    (covered : CoveredSourcePrimitive op)
    (source target sourceFinal : FlatSem.State C F) (values values' : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (states : StateRel cfg source target)
    (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src op) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src op) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases covered with
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
  | aupdate unsafeOp => exact doApp_arrayUpdate_complete cfg source target sourceFinal unsafeOp values values' result states related run
  | asub unsafeOp => exact doApp_arrayRead_complete cfg source target sourceFinal unsafeOp values values' result states related run
  | aw8sub unsafeOp => exact doApp_byteArrayRead_complete cfg source target sourceFinal unsafeOp values values' result states related run
  | aw8update unsafeOp => exact doApp_byteArrayUpdate_complete cfg source target sourceFinal unsafeOp values values' result states related run
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
  | vsub unsafeOp => exact doApp_vectorRead_related cfg source target sourceFinal unsafeOp values values' result states related run
  | ffi name => exact doApp_ffi_related cfg source target sourceFinal name values values' result states related run
  | allocThunk mode => exact doApp_thunkAlloc_related cfg source target sourceFinal mode values values' result states related run
  | updateThunk mode => exact doApp_thunkUpdate_related cfg source target sourceFinal mode values values' result states related run

/-- Flapjack intermediate for source operators in `do_app_thm`; HOL derives
the full theorem from `simple_do_app_thm`. -/
theorem doApp_source_related {C F : Type} (cfg : Config) (op : Op)
    (source target sourceFinal : FlatSem.State C F) (values values' : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (states : StateRel cfg source target)
    (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src op) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src op) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  by_cases call : op = .opapp
  · subst op
    simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  by_cases eval : op = .eval
  · subst op
    simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  by_cases force : op = .thunkOp .forceThunk
  · subst op
    simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  exact doApp_coveredSource_related cfg op (covered_simpleSourcePrimitive op call eval force)
    source target sourceFinal values values' result states related run

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
