module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Memory

@[expose] public section

/-! Thunk primitive operations under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

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

/-- Thunk-update validity agrees for related values and stores. -/
theorem badThunkUpdate_related {C F : Type} (source target : State C F)
    (mode : AstHOL.ThunkMode) (value nextValue : Value) (valueRel : ValueRel value nextValue)
    (states : StateRel source target) :
    badThunkUpdate mode value source.refs = badThunkUpdate mode nextValue target.refs := by
  have related := destThunk_related source target value nextValue valueRel states
  unfold badThunkUpdate
  split
  · cases left : destThunk [value] source.refs <;> cases right : destThunk [nextValue] target.refs <;>
      simp_all [DestThunkRel]
  · rfl

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

/-- Allocating a thunk keeps its stored values and fresh address related. -/
theorem primitiveSimulation_thunkAlloc {C F : Type} (mode : AstHOL.ThunkMode) :
    PrimitiveSimulation (C := C) (F := F) (.thunkOp (.allocThunk mode)) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp], by simp [doApp, AppResultRel, ResultRel]⟩
  | cons head tail =>
    cases tail with
    | nil =>
      rename_i value nextValue
      have same := badThunkUpdate_related source target mode value nextValue head states
      cases bad : badThunkUpdate mode value source.refs with
      | true =>
        have nextBad : badThunkUpdate mode nextValue target.refs = true := by rw [← same, bad]
        exact ⟨.err (.abort .typeError), by simp [doApp, nextBad], by simp [doApp, bad, AppResultRel, ResultRel]⟩
      | false =>
        have nextBad : badThunkUpdate mode nextValue target.refs = false := by rw [← same, bad]
        let index := leastUnusedRef source.refs
        have fresh : leastUnusedRef target.refs = index := (stateRel_leastUnusedRef source target states).symm
        have nextStates := stateRel_updateRefFfi source target states index (.thunk mode value)
          (.thunk mode nextValue) ⟨rfl, head⟩ source.ffi
        refine ⟨.val (.refPtr false index,
          { target with refs := target.refs.updateEq (index, .thunk mode nextValue) }), ?_, ?_⟩
        · simp [doApp, nextBad, fresh, index]
        · simp only [doApp, bad, Bool.false_eq_true, ↓reduceIte, AppResultRel]
          refine ⟨.refPtr false index, ?_⟩
          simpa [index, states.2.1] using nextStates
    | cons first rest =>
      exact ⟨.err (.abort .typeError), by simp [doApp], by simp [doApp, AppResultRel, ResultRel]⟩

/-- Updating an unevaluated thunk preserves related values and rejects the
same invalid pointers and thunk states. -/
theorem primitiveSimulation_thunkUpdate {C F : Type} (mode : AstHOL.ThunkMode) :
    PrimitiveSimulation (C := C) (F := F) (.thunkOp (.updateThunk mode)) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp], by simp [doApp, AppResultRel, ResultRel]⟩
  | cons first rest =>
    cases rest with
    | nil => exact ⟨.err (.abort .typeError), by simp [doApp], by simp [doApp, AppResultRel, ResultRel]⟩
    | cons second rest =>
      cases rest with
      | nil =>
        cases first with
        | refPtr flag index =>
          cases flag with
          | true => exact ⟨.err (.abort .typeError), by simp [doApp], by simp [doApp, AppResultRel, ResultRel]⟩
          | false =>
            rename_i value nextValue
            have same := badThunkUpdate_related source target mode value nextValue second states
            cases bad : badThunkUpdate mode value source.refs with
            | true =>
              have nextBad : badThunkUpdate mode nextValue target.refs = true := by rw [← same, bad]
              exact ⟨.err (.abort .typeError), by simp [doApp, nextBad], by simp [doApp, bad, AppResultRel, ResultRel]⟩
            | false =>
              have nextBad : badThunkUpdate mode nextValue target.refs = false := by rw [← same, bad]
              have refs := states.2.2.2.2.2.2.1 index
              cases left : source.refs.lookup index with
              | none =>
                cases right : target.refs.lookup index with
                | none => exact ⟨.err (.abort .typeError), by simp [doApp, nextBad, right], by
                    simp [doApp, bad, left, AppResultRel, ResultRel]⟩
                | some ref => simp [left, right, optionRel] at refs
              | some ref =>
                cases right : target.refs.lookup index with
                | none => simp [left, right, optionRel] at refs
                | some nextRef =>
                  have refRel : (ClosProps.refRel ValueRel) ref nextRef := by simpa [left, right, optionRel] using refs
                  cases ref with
                  | valueArray fields =>
                    cases nextRef <;> simp [ClosProps.refRel] at refRel
                    exact ⟨.err (.abort .typeError), by simp [doApp, nextBad, right], by
                      simp [doApp, bad, left, AppResultRel, ResultRel]⟩
                  | byteArray bytes =>
                    cases nextRef <;> simp [ClosProps.refRel] at refRel
                    exact ⟨.err (.abort .typeError), by simp [doApp, nextBad, right], by
                      simp [doApp, bad, left, AppResultRel, ResultRel]⟩
                  | thunk oldMode oldValue =>
                    cases nextRef with
                    | valueArray fields => simp [ClosProps.refRel] at refRel
                    | byteArray bytes => simp [ClosProps.refRel] at refRel
                    | thunk nextMode nextOldValue =>
                      obtain ⟨modeEq, oldValuesRel⟩ := refRel
                      subst nextMode
                      cases oldMode with
                      | evaluated =>
                        exact ⟨.err (.abort .typeError), by simp [doApp, nextBad, right], by
                          simp [doApp, bad, left, AppResultRel, ResultRel]⟩
                      | notEvaluated =>
                        have nextStates := stateRel_updateRefFfi source target states index (.thunk mode value)
                          (.thunk mode nextValue) ⟨rfl, second⟩ source.ffi
                        refine ⟨.val (unitValue, { target with refs := target.refs.updateEq (index, .thunk mode nextValue) }), ?_, ?_⟩
                        · simp [doApp, nextBad, right]
                        · simp only [doApp, bad, Bool.false_eq_true, ↓reduceIte, left, AppResultRel]
                          exact ⟨.block _ [] [] .nil, by simpa [states.2.1] using nextStates⟩
        | _ => exact ⟨.err (.abort .typeError), by simp [doApp], by simp [doApp, AppResultRel, ResultRel]⟩
      | cons third rest =>
        exact ⟨.err (.abort .typeError), by simp [doApp], by simp [doApp, AppResultRel, ResultRel]⟩

/-- The current proof-side primitive dispatcher is simulated for every ordinary
operation; installation and forcing have separate evaluator control flow. -/
theorem primitiveSimulation_ordinary {C F : Type} (op : ClosLang.Op)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk) :
    PrimitiveSimulation (C := C) (F := F) op := by
  cases op with
  | memOp operation => exact primitiveSimulation_memory operation
  | label label => exact primitiveSimulation_label label
  | ffi name => exact primitiveSimulation_ffi name
  | intOp operation => exact primitiveSimulation_int operation
  | wordOp operation => exact primitiveSimulation_word operation
  | blockOp operation => exact primitiveSimulation_block operation
  | globOp operation => exact primitiveSimulation_globalOp operation
  | thunkOp operation =>
    cases operation with
    | forceThunk => exact False.elim (notForce rfl)
    | allocThunk mode => exact primitiveSimulation_thunkAlloc mode
    | updateThunk mode => exact primitiveSimulation_thunkUpdate mode
  | install => exact False.elim (notInstall rfl)

end Flapjack.Compiler.Backend.ClosAnnotate
