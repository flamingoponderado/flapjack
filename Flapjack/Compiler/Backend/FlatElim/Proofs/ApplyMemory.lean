import Flapjack.Compiler.Backend.FlatElim.Proofs.PatternRelation
import Flapjack.Compiler.Backend.FlatProps.ResultValues
import Flapjack.EvaluateHOL
import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply

/-! Memory primitive cases for the flat-elimination simulation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- Reference assignment produces the same result in related states and
preserves their relation. This Flapjack helper covers successful assignments
with an explicit location/value argument pair; the general HOL primitive
simulation still requires the other operations and argument cases. -/
theorem doApp_assign_related {C F : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (flag : Bool) (address : Nat)
    (value : FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (related : flatStateRel reachable source target)
    (valueReachable : globalsWithin (findValueGlobals value) reachable)
    (valueSafe : valueHasEval value = false)
    (run : FlatSem.doApp source (.src .opassign) [.loc flag address, value] = some (next, result)) :
    ∃ targetNext, FlatSem.doApp target (.src .opassign) [.loc flag address, value] = some (targetNext, result) ∧
      flatStateRel reachable next targetNext ∧ result = .val FlatSem.unitValue := by
  have refsEq : source.refs = target.refs := related.2.1
  have run' : (do
      let refs ← storeAssign address (.refv value) source.refs
      some ({ source with refs := refs }, Result.val FlatSem.unitValue)) = some (next, result) := by
    simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] using run
  cases assigned : storeAssign address (.refv value) source.refs with
  | none => simp [assigned] at run'
  | some refs =>
    simp [assigned] at run'
    rcases run' with ⟨rfl, rfl⟩
    have assignSet : refs = source.refs.set address (.refv value) := by
      unfold storeAssign at assigned
      cases lookup : source.refs[address]? with
      | none => simp [lookup] at assigned
      | some old =>
        simp only [lookup] at assigned
        change (if storeValueSameType old (.refv value) then
          some (source.refs.set address (.refv value)) else none) = some refs at assigned
        split at assigned <;> simp_all
    subst refs
    refine ⟨{ target with refs := target.refs.set address (.refv value) }, ?_, ?_, rfl⟩
    · have targetAssign : storeAssign address (.refv value) target.refs =
          some (target.refs.set address (.refv value)) := by simpa [← refsEq] using assigned
      simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, targetAssign]
    · apply flatStateRel_setRefs reachable source target address (.refv value) related
      · exact valueReachable
      · simpa [storeHasNoEval] using valueSafe

/-- The assignment case of the original primitive simulation, with arbitrary
argument lists and the original result obligations. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "do_app_SOME_flat_state_rel"]
theorem doApp_some_flatStateRel_assign {C F G : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (_unusedRemovedState : G) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target)
    (_opNotApply : FlatLang.Op.src .opassign ≠ .src .opapp)
    (valuesReachable : globalsWithin (findValuesGlobals values) reachable)
    (_opReachable : globalsWithin (findLookups (.app tra (.src .opassign) [])) reachable)
    (valuesSafe : valuesNoEval values)
    (run : FlatSem.doApp source (.src .opassign) values = some (next, result))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, flatStateRel reachable next targetNext ∧
      FlatSem.doApp target (.src .opassign) values = some (targetNext, result) ∧
      globalsWithin (findPrimitiveResultGlobals (Flapjack.EvaluateHOL.listResult result)) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues
        (Flapjack.EvaluateHOL.listResult result)) := by
  cases values with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | cons value rest =>
      cases rest with
      | cons other rest => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
      | nil =>
        cases first <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
        case loc flag address =>
          have valueReachable : globalsWithin (findValueGlobals value) reachable := by
            have firstParts := (globalsWithin_union _ _ _).mp
              (by simpa [findValuesGlobals] using valuesReachable)
            exact ((globalsWithin_union _ _ _).mp
              (by simpa [findValuesGlobals] using firstParts.2)).1
          have valueSafe : valueHasEval value = false := valuesSafe value (by simp)
          obtain ⟨targetNext, targetRun, stateRel, rfl⟩ :=
            doApp_assign_related reachable source target next flag address value result related
              valueReachable valueSafe (by simpa [FlatSem.doApp, FlatSem.doAppNumeric,
                FlatSem.doAppMemory] using run)
          refine ⟨targetNext, stateRel, targetRun, ?_, ?_⟩
          · simp [findPrimitiveResultGlobals, Flapjack.EvaluateHOL.listResult,
              findValuesGlobals, findValueGlobals, FlatSem.unitValue, sptUnion, globalsWithin, sptMem, sptDomain]
          · simp [Flapjack.Compiler.Backend.FlatProps.resultValues, Flapjack.EvaluateHOL.listResult,
              valuesNoEval, FlatSem.unitValue, valueHasEval, valuesHaveEval]

end Flapjack.Compiler.Backend.FlatElim
