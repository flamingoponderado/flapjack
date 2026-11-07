import Flapjack.Compiler.Backend.FlatPattern.Proofs.ThunkRelation
import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply
import Flapjack.Misc.ListLookupRel

/-! Reference operations for the flat pattern compiler. These results use
the proof-side evaluator and relations, which remain pending HOL review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result storeAlloc storeAssign)
open Flapjack.SemanticPrimitivesProps (storeValueRel)

/-- Allocating a reference to related values produces related stores and the
same location. -/
theorem doApp_refAlloc_related {C F : Type} (cfg : Config)
    (source target : FlatSem.State C F) (values values' : List FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (sourceFinal : FlatSem.State C F) (result : FlatSem.Value)
    (run : FlatSem.doApp source (.src .opref) values = some (sourceFinal, .val result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .opref) values' = some (targetFinal, .val result') ∧
      StateRel cfg sourceFinal targetFinal ∧ ValueRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
  | @cons value value' tail tail' head rest =>
    cases rest with
    | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | nil =>
      simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, storeAlloc] at run
      rcases run with ⟨rfl, rfl⟩
      have lengths : target.refs.length = source.refs.length := (List.Forall₂.length_eq states.2.1).symm
      refine ⟨{ target with refs := target.refs ++ [.refv value'] }, .loc true target.refs.length, ?_, ?_, ?_⟩
      · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, storeAlloc]
      · exact ⟨states.1, List.rel_append states.2.1 (.cons head .nil), states.2.2⟩
      · exact (valueRel_loc true source.refs.length _).2 (by simp [lengths])

/-- A successful reference assignment preserves related stores and returns
related unit values. -/
theorem doApp_refAssign_related {C F : Type} (cfg : Config)
    (source target : FlatSem.State C F) (values values' : List FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (sourceFinal : FlatSem.State C F) (result : FlatSem.Value)
    (run : FlatSem.doApp source (.src .opassign) values = some (sourceFinal, .val result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .opassign) values' = some (targetFinal, .val result') ∧
      StateRel cfg sourceFinal targetFinal ∧ ValueRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
  | @cons loc loc' tail tail' locRel rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | @cons value value' tail tail' valueRel rest =>
      cases rest with
      | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
      | nil =>
        cases loc with
        | loc flag index =>
          have eq := (valueRel_loc flag index loc').1 locRel
          subst loc'
          cases assigned : storeAssign index (.refv value) source.refs with
          | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, assigned] at run
          | some refs =>
            have assigned' := SemanticPrimitivesProps.storeAssign_related states.2.1 index (show storeValueRel ValueRel (.refv value) (.refv value') from valueRel) assigned
            obtain ⟨refs', assignTarget, refsRel⟩ := assigned'
            simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, assigned] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨{ target with refs := refs' }, FlatSem.unitValue, ?_, ?_, ?_⟩
            · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, assignTarget]
            · exact ⟨states.1, refsRel, states.2.2⟩
            · exact (valueRel_conv none [] _).2 ⟨[], rfl, .nil⟩
        | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run

/-- Fixed-size array allocation stores the related argument lists and returns
the same newly allocated location. -/
theorem doApp_arrayFixed_related {C F : Type} (cfg : Config)
    (source target : FlatSem.State C F) (values values' : List FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values') :
    ∃ sourceFinal targetFinal result,
      FlatSem.doApp source (.src .aallocFixed) values = some (sourceFinal, .val result) ∧
      FlatSem.doApp target (.src .aallocFixed) values' = some (targetFinal, .val result) ∧
      StateRel cfg sourceFinal targetFinal ∧ ValueRel result result := by
  have lengths : target.refs.length = source.refs.length := (List.Forall₂.length_eq states.2.1).symm
  refine ⟨{ source with refs := source.refs ++ [.varray values] },
    { target with refs := target.refs ++ [.varray values'] }, .loc true source.refs.length, ?_, ?_, ?_, ?_⟩
  · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, storeAlloc]
  · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, storeAlloc, lengths]
  · exact ⟨states.1, List.rel_append states.2.1 (.cons related .nil), states.2.2⟩
  · exact (valueRel_loc true source.refs.length _).2 rfl

end Flapjack.Compiler.Backend.FlatPattern
