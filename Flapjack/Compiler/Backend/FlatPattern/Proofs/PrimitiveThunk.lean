import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveFFI

/-! Thunk primitives for the proof-side flat pattern simulation. The
evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result storeAlloc storeAssign)
open Flapjack.SemanticPrimitivesProps (storeValueRel)

/-- Related values and stores agree on whether a thunk update is invalid. -/
theorem badThunkUpdate_related (mode : ThunkMode) (value value' : FlatSem.Value)
    (store store' : Flapjack.SemanticPrimitivesHOL.Store FlatSem.Value)
    (values : ValueRel value value') (stores : List.Forall₂ (storeValueRel ValueRel) store store') :
    FlatSem.badThunkUpdate mode value store = FlatSem.badThunkUpdate mode value' store' := by
  cases mode with
  | notEvaluated => rfl
  | evaluated =>
    have related := destThunk_related (.cons values .nil) stores
    cases left : FlatSem.destThunk [value] store <;>
      cases right : FlatSem.destThunk [value'] store' <;>
      simp_all [DestThunkRel, FlatSem.badThunkUpdate]

/-- Successful thunk allocation preserves stores and the allocated location. -/
theorem doApp_thunkAlloc_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (mode : ThunkMode) (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src (.thunkOp (.allocThunk mode))) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src (.thunkOp (.allocThunk mode))) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | @cons value value' tail tail' values rest =>
    cases rest with
    | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | nil =>
      have badEq := badThunkUpdate_related mode value value' source.refs target.refs values states.2.1
      cases bad : FlatSem.badThunkUpdate mode value source.refs with
      | true => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, bad] at run
      | false =>
        have bad' : FlatSem.badThunkUpdate mode value' target.refs = false := by rw [← badEq, bad]
        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, storeAlloc, bad] at run
        rcases run with ⟨rfl, rfl⟩
        have lengths : target.refs.length = source.refs.length := (forall₂_length states.2.1).symm
        refine ⟨{ target with refs := target.refs ++ [.thunk mode value'] }, .val (.loc false source.refs.length), ?_, ?_, .value ?_⟩
        · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, storeAlloc, bad', lengths]
        · exact ⟨states.1, forall₂_append_one states.2.1 ⟨rfl, values⟩, states.2.2⟩
        · exact (valueRel_loc false source.refs.length _).2 rfl

/-- Successful explicit thunk updates preserve the related store. -/
theorem doApp_thunkUpdate_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (mode : ThunkMode) (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src (.thunkOp (.updateThunk mode))) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src (.thunkOp (.updateThunk mode))) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | @cons loc loc' tail tail' locRel rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | @cons value value' tail tail' valueRel rest =>
      cases rest with
      | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      | nil =>
        cases loc with
        | loc flag address =>
          have eq := (valueRel_loc flag address loc').1 locRel
          subst loc'
          cases flag with
          | true => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
          | false =>
            have badEq := badThunkUpdate_related mode value value' source.refs target.refs valueRel states.2.1
            cases bad : FlatSem.badThunkUpdate mode value source.refs with
            | true => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, bad] at run
            | false =>
              have bad' : FlatSem.badThunkUpdate mode value' target.refs = false := by rw [← badEq, bad]
              cases assigned : storeAssign address (.thunk mode value) source.refs with
              | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, bad, assigned] at run
              | some refs =>
                have entries : storeValueRel ValueRel (.thunk mode value) (.thunk mode value') := ⟨rfl, valueRel⟩
                obtain ⟨refs', assigned', refsRel⟩ := storeAssign_related states.2.1 address entries assigned
                simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, bad, assigned] at run
                rcases run with ⟨rfl, rfl⟩
                refine ⟨{ target with refs := refs' }, .val FlatSem.unitValue, ?_, ⟨states.1, refsRel, states.2.2⟩, .value ?_⟩
                · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, bad', assigned']
                · exact (valueRel_conv none [] _).2 ⟨[], rfl, .nil⟩
        | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run

end Flapjack.Compiler.Backend.FlatPattern
