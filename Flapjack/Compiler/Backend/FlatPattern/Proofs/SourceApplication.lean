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

end Flapjack.Compiler.Backend.FlatPattern
