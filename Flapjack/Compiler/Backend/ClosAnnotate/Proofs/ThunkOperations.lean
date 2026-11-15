module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Primitive
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.StateRelation.Original
public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

/-! Thunk primitive operations under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

private theorem stateRel_updateRefFfi {C F : Type} (source target : State C F) (states : StateRel source target)
    (index : Nat) (left right : Ref Value) (refsRel : (ClosProps.refRel ValueRel) left right) (ffi : HolFfiState F) :
    StateRel { source with refs := source.refs.updateEq (index, left), ffi := ffi }
      { target with refs := target.refs.updateEq (index, right), ffi := ffi } := by
  refine ⟨states.1, rfl, states.2.2.1, states.2.2.2.1, states.2.2.2.2.1,
    states.2.2.2.2.2.1, ?_, states.2.2.2.2.2.2.2⟩
  intro key
  by_cases same : key = index
  · subst key
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, optionRel] using refsRel
  · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same] using states.2.2.2.2.2.2.1 key

/-- Related thunk observations have the same status and related payloads. -/
def DestThunkRel : DestThunkResult → DestThunkResult → Prop
  | .badRef, .badRef | .notThunk, .notThunk => True
  | .isThunk mode left, .isThunk nextMode right => mode = nextMode ∧ ValueRel left right
  | _, _ => False

/-- Inspecting related values in related stores produces related thunk results. -/
theorem destThunk_related {C F : Type} (source target : State C F)
    (value nextValue : Value) (valueRel : ValueRel value nextValue) (states : StateRel source target) :
    DestThunkRel (destThunk [value] source.refs) (destThunk [nextValue] target.refs) := by
  cases valueRel with
  | refPtr flag index =>
    have refsRel := states.2.2.2.2.2.2.1 index
    cases left : source.refs.lookup index <;> cases right : target.refs.lookup index <;>
      simp_all [optionRel, ClosProps.refRel, destThunk, DestThunkRel]
    rename_i leftRef rightRef
    cases leftRef <;> cases rightRef <;> simp_all
    cases flag <;> simp_all
  | _ => simp [destThunk, DestThunkRel]

/-- Thunk inspection also agrees on non-singleton argument lists. -/
theorem destThunk_list_related {C F : Type} (source target : State C F)
    (values nextValues : List Value) (valuesRel : List.Forall₂ ValueRel values nextValues)
    (states : StateRel source target) : DestThunkRel (destThunk values source.refs) (destThunk nextValues target.refs) := by
  cases valuesRel with
  | nil => simp [destThunk, DestThunkRel]
  | cons first rest =>
    cases rest with
    | nil => exact destThunk_related source target _ _ first states
    | cons second rest => simp [destThunk, DestThunkRel]

/-- A force-result update succeeds or fails in both stores, and a successful
update preserves the candidate state relation. -/
theorem updateThunk_related {C F : Type} (source target : State C F)
    (values nextValues results nextResults : List Value)
    (valuesRel : List.Forall₂ ValueRel values nextValues)
    (resultsRel : List.Forall₂ ValueRel results nextResults)
    (states : StateRel source target) :
    match updateThunk values source.refs results with
    | none => updateThunk nextValues target.refs nextResults = none
    | some refs => ∃ nextRefs, updateThunk nextValues target.refs nextResults = some nextRefs ∧
        StateRel { source with refs := refs } { target with refs := nextRefs } := by
  cases valuesRel with
  | nil => simp [updateThunk]
  | cons pointer tail =>
    cases tail with
    | cons head tail => simp [updateThunk]
    | nil =>
      cases resultsRel with
      | nil => simp [updateThunk]
      | cons value tail =>
        cases tail with
        | cons head tail => simp [updateThunk]
        | nil =>
          cases pointer with
          | refPtr flag index =>
            cases flag with
            | true => simp [updateThunk]
            | false =>
              rename_i result nextResult
              have inspected := destThunk_related source target result nextResult value states
              cases left : destThunk [result] source.refs <;>
                cases right : destThunk [nextResult] target.refs <;>
                simp_all [DestThunkRel, updateThunk]
              have refsRel := states.2.2.2.2.2.2.1 index
              cases leftRef : source.refs.lookup index <;> cases rightRef : target.refs.lookup index <;>
                simp_all [optionRel, ClosProps.refRel, storeThunk]
              rename_i sourceRef targetRef
              cases sourceRef <;> cases targetRef <;> simp_all
              rename_i leftMode leftValue rightMode rightValue
              cases leftMode <;> cases rightMode <;> simp_all
              have updated := stateRel_updateRefFfi source target states index (.thunk .evaluated result)
                (.thunk .evaluated nextResult) ⟨rfl, value⟩ source.ffi
              simpa [states.2.1] using updated
          | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure =>
            simp [updateThunk]

namespace SourceThunkPort
/-- The canonical closure-state finite maps roundtrip through their broad view. -/
theorem holFmapAsFiniteSupportRelationWitness_State {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The existential reference map has the canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportExistentialWitness_relUpdateThunkSource_targetRefs
    (targetRefs : HolFiniteMapExact Nat (Ref Value)) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad targetRefs)).lookup = targetRefs.lookup ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad targetRefs)).finiteSupport = targetRefs.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad targetRefs) = targetRefs := by
  cases targetRefs
  exact ⟨rfl, rfl, rfl⟩
end SourceThunkPort

/-- A successful source thunk update yields a related target update. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "rel_update_thunk"
  (nested_list_rel_as_mutual := [FunctionsRel])
  (fmap_as_finite_support_relation := [State.refs, State.code, sourceRefs])
  (fmap_as_finite_support_existentials := [targetRefs])]
theorem relUpdateThunkSource {C F : Type} (source target : ClosSem.State C F) (flag : Bool) (ptr : Nat)
    (values nextValues : List Value) (sourceRefs : HolFiniteMapExact Nat (Ref Value))
    (related : StateRelSource source target ∧ List.Forall₂ ValueRel values nextValues)
    (updated : updateThunk [.refPtr flag ptr] source.refs values = some sourceRefs) :
    ∃ targetRefs : HolFiniteMapExact Nat (Ref Value),
      updateThunk [.refPtr flag ptr] target.refs nextValues = some targetRefs ∧
        StateRelSource { source with refs := sourceRefs } { target with refs := targetRefs } := by
  have live := (stateRelSource_iff source target).mp related.1
  have update := updateThunk_related source target [.refPtr flag ptr] [.refPtr flag ptr]
    values nextValues (.cons (.refPtr flag ptr) .nil) related.2 live
  rw [updated] at update
  obtain ⟨targetRefs, run, states⟩ := update
  exact ⟨targetRefs, run, (stateRelSource_iff _ _).mpr states⟩

end Flapjack.Compiler.Backend.ClosAnnotate
