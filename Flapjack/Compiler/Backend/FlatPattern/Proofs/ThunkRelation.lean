import Flapjack.Compiler.Backend.FlatPattern.Proofs.PatternRelation
import Flapjack.Compiler.Backend.Semantics.FlatSem.Thunk

/-! Store and thunk relations used by the flat pattern pass. These results use
the proof-side value relation, which remains pending comparison with HOL. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (Store StoreValue storeLookup storeAssign storeValueSameType)
open Flapjack.SemanticPrimitivesProps

/-- Thunk inspection either agrees on the non-value outcomes or returns
thunks with the same mode and related contents. -/
def DestThunkRel : DestThunkResult → DestThunkResult → Prop
  | .badRef, .badRef | .notThunk, .notThunk => True
  | .isThunk mode value, .isThunk mode' value' => mode = mode' ∧ ValueRel value value'
  | _, _ => False

/-- Inspection preserves the outcome for related arguments and stores. -/
theorem destThunk_related {left right : List Value} {store store' : Store Value}
    (values : List.Forall₂ ValueRel left right)
    (stores : List.Forall₂ (storeValueRel ValueRel) store store') :
    DestThunkRel (destThunk left store) (destThunk right store') := by
  cases values with
  | nil => simp [destThunk, DestThunkRel]
  | @cons value value' tail tail' head rest =>
    cases rest with
    | cons _ _ => simp [destThunk, DestThunkRel]
    | nil =>
      cases value with
      | loc flag index =>
        have eq := (valueRel_loc flag index value').1 head
        subst value'
        cases found : storeLookup index store with
        | none =>
          have absent := SemanticPrimitivesProps.storeValueRel_lookup_none stores index found
          simp [destThunk, found, absent, DestThunkRel]
        | some entry =>
          obtain ⟨entry', found', rel⟩ := SemanticPrimitivesProps.storeValueRel_lookup stores index entry found
          cases flag <;> cases entry <;> cases entry' <;> simp_all [storeValueRel, destThunk, DestThunkRel]
      | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        cases value' <;> cases head <;> simp_all [FlatProps.simpleBasicValRel, destThunk, DestThunkRel]

/-- Updating related thunk stores preserves the store relation whenever the
source update succeeds. -/
theorem updateThunk_related {targets targets' values values' : List Value}
    {store store' result : Store Value}
    (targetRel : List.Forall₂ ValueRel targets targets')
    (valueRel : List.Forall₂ ValueRel values values')
    (stores : List.Forall₂ (storeValueRel ValueRel) store store')
    (updated : updateThunk targets store values = some result) :
    ∃ result', updateThunk targets' store' values' = some result' ∧
      List.Forall₂ (storeValueRel ValueRel) result result' := by
  cases targetRel with
  | nil => simp [updateThunk] at updated
  | @cons target target' tail tail' head rest =>
    cases rest with
    | cons _ _ => simp [updateThunk] at updated
    | nil =>
      cases valueRel with
      | nil => simp [updateThunk] at updated
      | @cons value value' tail tail' valueHead valueTail =>
        cases valueTail with
        | cons _ _ => simp [updateThunk] at updated
        | nil =>
          cases target with
          | loc flag index =>
            have eq := (valueRel_loc flag index target').1 head
            subst target'
            cases flag with
            | true => simp [updateThunk] at updated
            | false =>
              have inspected := destThunk_related (List.Forall₂.cons valueHead .nil) stores
              cases outcome : destThunk [value] store with
              | badRef => simp [updateThunk, outcome] at updated
              | isThunk _ _ => simp [updateThunk, outcome] at updated
              | notThunk =>
                cases outcome' : destThunk [value'] store' with
                | badRef | isThunk _ _ => simp [outcome, outcome', DestThunkRel] at inspected
                | notThunk =>
                  have assigned : storeAssign index (.thunk .evaluated value) store = some result := by
                    simpa [updateThunk, outcome] using updated
                  obtain ⟨result', assigned', rel⟩ := SemanticPrimitivesProps.storeAssign_related stores index
                    (show storeValueRel ValueRel (.thunk .evaluated value) (.thunk .evaluated value') from ⟨rfl, valueHead⟩) assigned
                  exact ⟨result', by simpa [updateThunk, outcome'] using assigned', rel⟩
          | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
            simp [updateThunk] at updated

end Flapjack.Compiler.Backend.FlatPattern
