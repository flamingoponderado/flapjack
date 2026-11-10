module

public import Flapjack.FiniteMap.BroadCodec

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Primitive
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Thunk

@[expose] public section

/-! Reference-store prerequisites for thunk forcing. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem

/-- Thunk inspection retains its outcome and relates stored values. This is
Flapjack infrastructure for the thunk-forcing proof. -/
def DestThunkRel : DestThunkResult → DestThunkResult → Prop
  | .badRef, .badRef | .notThunk, .notThunk => True
  | .isThunk mode left, .isThunk nextMode right => mode = nextMode ∧ ValueRel left right
  | _, _ => False

/-- Inspection of related singleton values in related stores agrees. This is
Flapjack infrastructure for the thunk-forcing proof. -/
theorem destThunk_related {C F : Type} (source target : State C F) (value nextValue : Value)
    (values : ValueRel value nextValue) (states : StateRel source target) :
    DestThunkRel (destThunk [value] source.refs) (destThunk [nextValue] target.refs) := by
  cases values with
  | refPtr flag index =>
    have refs := states.2.2.2.2.2.2.2.2.1 index
    cases left : source.refs.lookup index <;> cases right : target.refs.lookup index <;>
      simp_all [Flapjack.optionRel, destThunk, DestThunkRel]
    cases refs with
    | byteArray bytes => simp
    | valueArray xs ys related => simp
    | thunk mode x y related => cases flag <;> simp [related]
  | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure =>
    simp [destThunk, DestThunkRel]

/-- Inspection also agrees for lists with an invalid number of operands. This
is Flapjack infrastructure for the thunk-forcing proof. -/
theorem destThunk_list_related {C F : Type} (source target : State C F) (values nextValues : List Value)
    (related : List.Forall₂ ValueRel values nextValues) (states : StateRel source target) :
    DestThunkRel (destThunk values source.refs) (destThunk nextValues target.refs) := by
  cases related with
  | nil => simp [destThunk, DestThunkRel]
  | cons head tail =>
    cases tail with
    | nil => exact destThunk_related source target _ _ head states
    | cons next tail => simp [destThunk, DestThunkRel]

/-- Updating corresponding reference entries preserves the state relation.
This is Flapjack infrastructure for the thunk-forcing proof. -/
theorem stateRel_updateRefs {C F : Type} (source target : State C F) (index : Nat)
    (left right : Ref Value) (states : StateRel source target) (values : RefRel left right) :
    StateRel { source with refs := source.refs.updateEq (index, left) }
      { target with refs := target.refs.updateEq (index, right) } := by
  obtain ⟨aux, codeS, codeT, maxApp, positive, clock, ffi, globals, refs, compiler, oracle⟩ := states
  exact ⟨aux, codeS, codeT, maxApp, positive, clock, ffi, globals,
    refLookup_update source target index left right refs values, compiler, oracle⟩

/-- Thunk updates fail together or produce related stores. This is Flapjack
infrastructure for the thunk-forcing proof. -/
theorem updateThunk_related {C F : Type} (source target : State C F)
    (values nextValues results nextResults : List Value)
    (valuesRel : List.Forall₂ ValueRel values nextValues)
    (resultsRel : List.Forall₂ ValueRel results nextResults) (states : StateRel source target) :
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
              have refs := states.2.2.2.2.2.2.2.2.1 index
              cases leftRef : source.refs.lookup index <;> cases rightRef : target.refs.lookup index <;>
                simp_all [Flapjack.optionRel, storeThunk]
              cases refs with
              | byteArray bytes => simp_all
              | valueArray xs ys related => simp_all
              | thunk mode x y related =>
                cases mode <;> simp_all
                exact stateRel_updateRefs source target index (.thunk .evaluated result)
                  (.thunk .evaluated nextResult) states (.thunk .evaluated result nextResult value)
          | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure =>
            simp [updateThunk]

namespace ForcePort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_State {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Canonical codec for the existential reference-map witness. -/
theorem holFmapAsFiniteSupportExistentialWitness_rel_update_thunk_sourceRefs
    (sourceRefs : HolFiniteMapExact Nat (Ref Value)) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sourceRefs)).lookup = sourceRefs.lookup ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sourceRefs)).finiteSupport = sourceRefs.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sourceRefs) = sourceRefs := by
  cases sourceRefs
  exact ⟨rfl, rfl, rfl⟩

/-- A related target thunk update fails on both sides or produces related states. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "rel_update_thunk"
  (fmap_as_finite_support_relation := [State.refs, State.code, targetRefs])
  (fmap_as_finite_support_existentials := [sourceRefs])]
theorem rel_update_thunk {C F : Type} (source target : State C F) (flag : Bool) (ptr : Nat)
    (values nextValues : List Value) (targetRefs : HolFiniteMapExact Nat (Ref Value))
    (related : StateRel source target ∧ List.Forall₂ ValueRel values nextValues) :
    (updateThunk [.refPtr flag ptr] target.refs nextValues = none →
      updateThunk [.refPtr flag ptr] source.refs values = none) ∧
    (updateThunk [.refPtr flag ptr] target.refs nextValues = some targetRefs →
      ∃ (sourceRefs : HolFiniteMapExact Nat (Ref Value)),
        updateThunk [.refPtr flag ptr] source.refs values = some sourceRefs ∧
        StateRel { source with refs := sourceRefs } { target with refs := targetRefs }) := by
  have update := updateThunk_related source target [.refPtr flag ptr] [.refPtr flag ptr] values nextValues
    (.cons (.refPtr flag ptr) .nil) related.2 related.1
  cases sourceRun : updateThunk [.refPtr flag ptr] source.refs values with
  | none =>
    have targetRun : updateThunk [.refPtr flag ptr] target.refs nextValues = none := by simpa [sourceRun] using update
    simp [targetRun]
  | some sourceRefs =>
    obtain ⟨actualTargetRefs, targetRun, nextRel⟩ := by simpa [sourceRun] using update
    constructor
    · intro h; simp [targetRun] at h
    · intro h
      have equal : actualTargetRefs = targetRefs := by simpa [targetRun] using h
      subst targetRefs
      exact ⟨sourceRefs, rfl, nextRel⟩
end ForcePort

end Flapjack.Compiler.Backend.ClosTicks
