import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveByteArray

/-! Foreign calls for the proof-side flat pattern simulation. The evaluator
and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result storeLookup storeAssign)
open Flapjack.SemanticPrimitivesProps (storeValueRel)

/-- Successful foreign calls preserve their observable event, output bytes,
and resulting state for related argument values and stores. -/
theorem doApp_ffi_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (name : Flapjack.Basis.Pure.MlString.MlString) (values values' : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (states : StateRel cfg source target)
    (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src (.ffi name)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src (.ffi name)) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | @cons config config' tail tail' configRel rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | @cons loc loc' tail tail' locRel rest =>
      cases rest with
      | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      | nil =>
        cases config with
        | litv literal =>
          have configEq := (valueRel_lit literal config').1 configRel
          subst config'
          cases literal with
          | strLit configuration =>
            cases loc with
            | loc flag address =>
              have locEq := (valueRel_loc flag address loc').1 locRel
              subst loc'
              cases found : storeLookup address source.refs with
              | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, found] at run
              | some entry =>
                cases entry with
                | w8array bytes =>
                  have found' := stateRel_lookup_bytes cfg source target states address bytes found
                  have ffiEq := states.2.2.1
                  cases called : Flapjack.callFFIHOL source.ffi (.extCall name) configuration.explode bytes with
                  | final event =>
                    simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, found, called] at run
                    rcases run with ⟨rfl, rfl⟩
                    refine ⟨target, .err (.abort (.ffiError event)), ?_, states, .error (.abort _)⟩
                    simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, found', ffiEq, called]
                  | ret ffi bytes' =>
                    cases assigned : storeAssign address (.w8array bytes') source.refs with
                    | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, found, called, assigned] at run
                    | some refs =>
                      have entries : storeValueRel ValueRel (.w8array bytes') (.w8array bytes') := rfl
                      obtain ⟨refs', assigned', refsRel⟩ := storeAssign_related states.2.1 address entries assigned
                      simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, found, called, assigned] at run
                      rcases run with ⟨rfl, rfl⟩
                      refine ⟨{ target with refs := refs', ffi := ffi }, .val FlatSem.unitValue, ?_, ?_, .value ?_⟩
                      · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, found', ffiEq, called, assigned']
                      · exact ⟨states.1, refsRel, rfl, states.2.2.2⟩
                      · exact (valueRel_conv none [] _).2 ⟨[], rfl, .nil⟩
                | refv _ | varray _ | thunk _ _ =>
                  simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, found] at run
            | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
              simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
          | intLit _ | word8 _ | word64 _ | char _ | float64 _ =>
            simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
        | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run

end Flapjack.Compiler.Backend.FlatPattern
