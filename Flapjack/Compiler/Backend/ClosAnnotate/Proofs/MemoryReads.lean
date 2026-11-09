import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.MemoryAllocation

/-! Reference inspection under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- The observed length of a reference, selected by the expected array type. -/
def refLength (byte : Bool) : Option (Ref Value) → Option Value
  | some (.valueArray values) => if byte then none else some (.number values.length)
  | some (.byteArray bytes) => if byte then some (.number bytes.length) else none
  | _ => none

/-- Related reference payloads have identical valid length observations. -/
theorem refLength_related (byte : Bool) (left right : Option (Ref Value))
    (related : optionRel (ClosProps.refRel ValueRel) left right) : optionRel ValueRel (refLength byte left) (refLength byte right) := by
  cases left with
  | none => cases right <;> simp_all [optionRel, refLength]
  | some leftRef =>
    cases right with
    | none => simp [optionRel] at related
    | some rightRef =>
      cases leftRef with
      | valueArray fields =>
        cases rightRef with
        | valueArray nextFields =>
          have len := related.length_eq
          cases byte <;> simp [refLength, optionRel, ← len, ValueRel.number]
        | _ => simp [optionRel, ClosProps.refRel] at related
      | byteArray bytes =>
        cases rightRef with
        | byteArray nextBytes =>
          have same : bytes = nextBytes := related
          subst nextBytes
          cases byte <;> simp [refLength, optionRel, ValueRel.number]
        | _ => simp [optionRel, ClosProps.refRel] at related
      | thunk mode value =>
        cases rightRef <;> simp_all [optionRel, ClosProps.refRel, refLength]

/-- The length cases of the dispatcher expose the reference observation. -/
theorem applyMemory_refLength {C F : Type} (byte flag : Bool) (index : Nat) (state : State C F) :
    applyMemory (if byte then .lengthByte else .length) [.refPtr flag index] state =
      (refLength byte (state.refs.lookup index)).map (fun value => (value, state)) := by
  cases byte <;> cases h : state.refs.lookup index with
  | none => simp [applyMemory, refLength, h]
  | some ref => cases ref <;> simp [applyMemory, refLength, h]

/-- Reading either value-array or byte-array lengths preserves the primitive
relation, including the same failure on a missing or wrong-kind reference. -/
theorem primitiveSimulation_refLength {C F : Type} (byte : Bool) :
    PrimitiveSimulation (C := C) (F := F) (.memOp (if byte then .lengthByte else .length)) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => cases byte <;>
    exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | refPtr flag index =>
        have observed := refLength_related byte (source.refs.lookup index) (target.refs.lookup index)
          (states.2.2.2.2.2.2.1 index)
        obtain ⟨outcome, nextRun, rel⟩ := pureOption_result _ _ source target observed states
        have sourceEquation := applyMemory_refLength byte flag index source
        have targetEquation := applyMemory_refLength byte flag index target
        refine ⟨outcome, ?_, ?_⟩
        · cases h : refLength byte (target.refs.lookup index) <;>
            simpa [doApp, targetEquation, h] using nextRun
        · cases h : refLength byte (source.refs.lookup index) <;>
            simpa [doApp, sourceEquation, h] using rel
      | _ => cases byte <;>
          exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons first rest => cases byte <;>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

/-- Extract a value array from an optional reference. -/
def refValueArray : Option (Ref Value) → Option (List Value)
  | some (.valueArray values) => some values
  | _ => none

/-- Related references contain related value arrays or both fail extraction. -/
theorem refValueArray_related (left right : Option (Ref Value)) (related : optionRel (ClosProps.refRel ValueRel) left right) :
    optionRel (List.Forall₂ ValueRel) (refValueArray left) (refValueArray right) := by
  cases left with
  | none => cases right <;> simp_all [optionRel, refValueArray]
  | some leftRef =>
    cases right with
    | none => simp [optionRel] at related
    | some rightRef => cases leftRef <;> cases rightRef <;> simp_all [optionRel, ClosProps.refRel, refValueArray]

/-- An indexed value observation from a block or value-array reference. -/
def valueAt (value : Value) (index : Int) (refs : HolFiniteMapExact Nat (Ref Value)) : Option Value :=
  if index < 0 then none else
    match value with
    | .block _ fields => fields[index.toNat]?
    | .refPtr _ ptr => (refValueArray (refs.lookup ptr)).bind (fun fields => fields[index.toNat]?)
    | _ => none

/-- Related blocks and stores produce related indexed observations. -/
theorem valueAt_related {C F : Type} (value nextValue : Value) (related : ValueRel value nextValue)
    (index : Int) (source target : State C F) (states : StateRel source target) :
    optionRel ValueRel (valueAt value index source.refs) (valueAt nextValue index target.refs) := by
  by_cases negative : index < 0
  · simp [valueAt, negative, optionRel]
  · cases related with
    | block tag fields nextFields fieldsRel =>
      simpa [valueAt, negative] using optionRel_getElem fields nextFields fieldsRel index.toNat
    | refPtr flag ptr =>
      have arrays := refValueArray_related (source.refs.lookup ptr) (target.refs.lookup ptr)
        (states.2.2.2.2.2.2.1 ptr)
      cases left : refValueArray (source.refs.lookup ptr) with
      | none =>
        cases right : refValueArray (target.refs.lookup ptr) <;> simp_all [valueAt, optionRel]
      | some fields =>
        cases right : refValueArray (target.refs.lookup ptr) with
        | none => simp [left, right, optionRel] at arrays
        | some nextFields =>
          have fieldsRel : List.Forall₂ ValueRel fields nextFields := by simpa [left, right, optionRel] using arrays
          simpa [valueAt, negative, left, right] using optionRel_getElem fields nextFields fieldsRel index.toNat
    | _ => simp [valueAt, negative, optionRel]

/-- The evaluator's indexed-read dispatcher exposes the indexed observation. -/
theorem applyMemory_valueAt {C F : Type} (value : Value) (index : Int) (state : State C F) :
    applyMemory .el [value, .number index] state = (valueAt value index state.refs).map (fun x => (x, state)) := by
  cases value with
  | block tag fields =>
    by_cases negative : index < 0 <;> simp [applyMemory, valueAt, negative, Option.map_eq_bind]
  | refPtr flag ptr =>
    cases h : state.refs.lookup ptr with
    | none => simp [applyMemory, valueAt, refValueArray, h]
    | some ref =>
      cases ref with
      | valueArray fields =>
        by_cases negative : index < 0 <;> simp [applyMemory, valueAt, refValueArray, h, negative,
          Option.map_eq_bind]
      | _ => simp [applyMemory, valueAt, refValueArray, h]
  | _ => simp [applyMemory, valueAt]

/-- Indexed block and value-array reads preserve the candidate simulation. -/
theorem primitiveSimulation_el {C F : Type} : PrimitiveSimulation (C := C) (F := F) (.memOp .el) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons first rest =>
    cases rest with
    | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons second rest =>
      cases rest with
      | nil =>
        cases second with
        | number index =>
          rename_i value nextValue
          have observed := valueAt_related value nextValue first index source target states
          obtain ⟨outcome, nextRun, rel⟩ := pureOption_result _ _ source target observed states
          refine ⟨outcome, ?_, ?_⟩
          · cases h : valueAt nextValue index target.refs <;>
              simpa [doApp, applyMemory_valueAt, h] using nextRun
          · cases h : valueAt value index source.refs <;>
              simpa [doApp, applyMemory_valueAt, h] using rel
        | _ => cases first <;>
            exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
      | cons third rest =>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

end Flapjack.Compiler.Backend.ClosAnnotate
