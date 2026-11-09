import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.MemoryUpdates

/-! Array bounds and configuration observations under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- A value-array reference produces its optional bounds-check result. -/
def arrayBounds (index : Int) (ref : Option (Ref Value)) : Option Value :=
  (refValueArray ref).map (fun fields => boolValue (decide (0 ≤ index ∧ index < Int.ofNat fields.length)))

/-- Related value-array references produce related bounds observations. -/
theorem arrayBounds_related (index : Int) (left right : Option (Ref Value)) (related : optionRel (ClosProps.refRel ValueRel) left right) :
    optionRel ValueRel (arrayBounds index left) (arrayBounds index right) := by
  have arrays := refValueArray_related left right related
  cases leftRun : refValueArray left with
  | none => cases rightRun : refValueArray right <;> simp_all [arrayBounds, optionRel]
  | some fields =>
    cases rightRun : refValueArray right with
    | none => simp [leftRun, rightRun, optionRel] at arrays
    | some nextFields =>
      have fieldsRel : List.Forall₂ ValueRel fields nextFields := by simpa [leftRun, rightRun, optionRel] using arrays
      simp only [arrayBounds, leftRun, rightRun, Option.map, optionRel]
      rw [fieldsRel.length_eq]
      exact .block _ [] [] .nil

/-- Array bounds checking exposes the optional observation on a reference. -/
theorem applyMemory_arrayBounds {C F : Type} (flag : Bool) (ptr : Nat) (index : Int) (state : State C F) :
    applyMemory .boundsCheckArray [.refPtr flag ptr, .number index] state =
      (arrayBounds index (state.refs.lookup ptr)).map (fun result => (result, state)) := by
  cases h : state.refs.lookup ptr with
  | none => simp [applyMemory, arrayBounds, refValueArray, h]
  | some ref => cases ref <;> simp [applyMemory, arrayBounds, refValueArray, h]

/-- Value-array bounds checks preserve the candidate primitive simulation. -/
theorem primitiveSimulation_boundsCheckArray {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.memOp .boundsCheckArray) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons first rest =>
    cases rest with
    | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons second rest =>
      cases rest with
      | nil =>
        cases first with
        | refPtr flag ptr =>
          cases second with
          | number index =>
            have observed := arrayBounds_related index (source.refs.lookup ptr) (target.refs.lookup ptr)
              (states.2.2.2.2.2.2.1 ptr)
            obtain ⟨outcome, nextRun, rel⟩ := pureOption_result _ _ source target observed states
            refine ⟨outcome, ?_, ?_⟩
            · cases h : arrayBounds index (target.refs.lookup ptr) <;>
                simpa [doApp, applyMemory_arrayBounds, h] using nextRun
            · cases h : arrayBounds index (source.refs.lookup ptr) <;>
                simpa [doApp, applyMemory_arrayBounds, h] using rel
          | _ => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
        | _ => cases second <;>
            exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
      | cons third rest =>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

/-- The current proof-side GC configuration operation preserves the state. -/
theorem primitiveSimulation_configGC {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.memOp .configGC) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons first rest =>
    cases rest with
    | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons second rest =>
      cases rest with
      | nil =>
        cases first <;> cases second <;> simp [doApp, applyMemory, AppResultRel, ResultRel, states]
        exact .block _ [] [] .nil
      | cons third rest =>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

end Flapjack.Compiler.Backend.ClosAnnotate
