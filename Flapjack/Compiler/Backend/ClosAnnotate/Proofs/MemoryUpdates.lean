import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.MemoryReads

/-! Mutable value-array operations under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Related stores agree on value-array updates, including invalid references
and indices. -/
theorem updateArray_related {C F : Type} (source target : State C F) (states : StateRel source target)
    (flag : Bool) (ptr : Nat) (index : Int) (value nextValue : Value) (valuesRel : ValueRel value nextValue) :
    ∃ outcome, doApp (.memOp .update) [.refPtr flag ptr, .number index, nextValue] target = outcome ∧
      AppResultRel (doApp (.memOp .update) [.refPtr flag ptr, .number index, value] source) outcome := by
  have refs := states.2.2.2.2.2.2.1 ptr
  cases left : source.refs.lookup ptr with
  | none =>
    cases right : target.refs.lookup ptr with
    | none => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory, right], by
        simp [doApp, applyMemory, left, AppResultRel, ResultRel]⟩
    | some ref => simp [left, right, optionRel] at refs
  | some ref =>
    cases right : target.refs.lookup ptr with
    | none => simp [left, right, optionRel] at refs
    | some nextRef =>
      have refRel : (ClosProps.refRel ValueRel) ref nextRef := by simpa [left, right, optionRel] using refs
      cases ref with
      | byteArray bytes =>
        cases nextRef <;> simp [ClosProps.refRel] at refRel
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory, right], by
          simp [doApp, applyMemory, left, AppResultRel, ResultRel]⟩
      | thunk mode v =>
        cases nextRef <;> simp [ClosProps.refRel] at refRel
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory, right], by
          simp [doApp, applyMemory, left, AppResultRel, ResultRel]⟩
      | valueArray fields =>
        cases nextRef with
        | byteArray bytes => simp [ClosProps.refRel] at refRel
        | thunk mode v => simp [ClosProps.refRel] at refRel
        | valueArray nextFields =>
          have fieldsRel : List.Forall₂ ValueRel fields nextFields := refRel
          have sameLength := fieldsRel.length_eq
          by_cases invalid : index < 0 ∨ index.toNat ≥ fields.length
          · refine ⟨.err (.abort .typeError), ?_, ?_⟩
            · simp only [doApp, applyMemory, right, ← sameLength, if_pos invalid]
            · simp only [doApp, applyMemory, left, if_pos invalid, AppResultRel, ResultRel]
          · have updated := Flapjack.forall₂_set _ fields nextFields value nextValue index.toNat ⟨valuesRel, fieldsRel⟩
            have nextStates := stateRel_updateRefFfi source target states ptr
              (.valueArray (fields.set index.toNat value)) (.valueArray (nextFields.set index.toNat nextValue))
              updated source.ffi
            refine ⟨.val (unitValue,
              { target with refs := target.refs.updateEq (ptr, .valueArray (nextFields.set index.toNat nextValue)) }), ?_, ?_⟩
            · simp only [doApp, applyMemory, right, ← sameLength, if_neg invalid]
            · simp only [doApp, applyMemory, left, if_neg invalid, AppResultRel]
              refine ⟨.block _ [] [] .nil, ?_⟩
              simpa [states.2.1] using nextStates

/-- Value-array update preserves the candidate primitive simulation. -/
theorem primitiveSimulation_update {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.memOp .update) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons first rest =>
    cases rest with
    | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons second rest =>
      cases rest with
      | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
      | cons third rest =>
        cases rest with
        | nil =>
          cases first with
          | refPtr flag ptr =>
            cases second with
            | number index => exact updateArray_related source target states flag ptr index _ _ third
            | _ => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
          | _ => cases second <;>
              exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
        | cons fourth rest =>
          exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

/-- A byte-array write either fails on both sides or updates identical bytes. -/
theorem updateByte_related {C F : Type} (source target : State C F) (states : StateRel source target)
    (flag : Bool) (ptr : Nat) (index byte : Int) :
    ∃ outcome, doApp (.memOp .updateByte) [.refPtr flag ptr, .number index, .number byte] target = outcome ∧
      AppResultRel (doApp (.memOp .updateByte) [.refPtr flag ptr, .number index, .number byte] source) outcome := by
  have refs := states.2.2.2.2.2.2.1 ptr
  cases left : source.refs.lookup ptr with
  | none =>
    cases right : target.refs.lookup ptr with
    | none => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory, right], by
        simp [doApp, applyMemory, left, AppResultRel, ResultRel]⟩
    | some ref => simp [left, right, optionRel] at refs
  | some ref =>
    cases right : target.refs.lookup ptr with
    | none => simp [left, right, optionRel] at refs
    | some nextRef =>
      have refRel : (ClosProps.refRel ValueRel) ref nextRef := by simpa [left, right, optionRel] using refs
      cases ref with
      | valueArray fields =>
        cases nextRef <;> simp [ClosProps.refRel] at refRel
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory, right], by
          simp [doApp, applyMemory, left, AppResultRel, ResultRel]⟩
      | thunk mode v =>
        cases nextRef <;> simp [ClosProps.refRel] at refRel
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory, right], by
          simp [doApp, applyMemory, left, AppResultRel, ResultRel]⟩
      | byteArray bytes =>
        cases nextRef with
        | valueArray fields => simp [ClosProps.refRel] at refRel
        | thunk mode v => simp [ClosProps.refRel] at refRel
        | byteArray nextBytes =>
          have equal : bytes = nextBytes := refRel
          subst nextBytes
          by_cases invalid : index < 0 ∨ index.toNat ≥ bytes.length
          · refine ⟨.err (.abort .typeError), ?_, ?_⟩
            · simp only [doApp, applyMemory, right, if_pos invalid]
            · simp only [doApp, applyMemory, left, if_pos invalid, AppResultRel, ResultRel]
          · cases decoded : intToByte byte with
            | none =>
              exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory, right, invalid, decoded], by
                simp [doApp, applyMemory, left, invalid, decoded, AppResultRel, ResultRel]⟩
            | some b =>
              have nextStates := stateRel_updateRefFfi source target states ptr
                (.byteArray (bytes.set index.toNat b)) (.byteArray (bytes.set index.toNat b)) rfl source.ffi
              refine ⟨.val (unitValue,
                { target with refs := target.refs.updateEq (ptr, .byteArray (bytes.set index.toNat b)) }), ?_, ?_⟩
              · simp [doApp, applyMemory, right, invalid, decoded]
              · simp only [doApp, applyMemory, left, if_neg invalid, decoded, AppResultRel]
                refine ⟨.block _ [] [] .nil, ?_⟩
                simpa [states.2.1] using nextStates

/-- Byte-array updates preserve the candidate primitive simulation. -/
theorem primitiveSimulation_updateByte {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.memOp .updateByte) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons first rest =>
    cases rest with
    | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons second rest =>
      cases rest with
      | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
      | cons third rest =>
        cases rest with
        | nil =>
          cases first with
          | refPtr flag ptr =>
            cases second with
            | number index =>
              cases third with
              | number byte => exact updateByte_related source target states flag ptr index byte
              | _ => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
            | _ => cases third <;>
                exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
          | _ => cases second <;> cases third <;>
              exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
        | cons fourth rest =>
          exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

end Flapjack.Compiler.Backend.ClosAnnotate
