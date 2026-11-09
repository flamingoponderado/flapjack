module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.ByteReads

@[expose] public section

/-! Byte-array update operations under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- XOR with a related byte-array reference agrees on failure and preserves
the candidate state relation after a successful update. -/
theorem xorByte_related {C F : Type} (source target : State C F) (states : StateRel source target)
    (flag : Bool) (ptr : Nat) (input : List (BitVec 8)) :
    ∃ outcome, doApp (.memOp .xorByte) [.refPtr flag ptr, .byteVector input] target = outcome ∧
      AppResultRel (doApp (.memOp .xorByte) [.refPtr flag ptr, .byteVector input] source) outcome := by
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
      have refRel : RefRel ref nextRef := by simpa [left, right, optionRel] using refs
      cases ref with
      | valueArray fields =>
        cases nextRef <;> simp [RefRel] at refRel
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory, right], by
          simp [doApp, applyMemory, left, AppResultRel, ResultRel]⟩
      | thunk mode value =>
        cases nextRef <;> simp [RefRel] at refRel
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory, right], by
          simp [doApp, applyMemory, left, AppResultRel, ResultRel]⟩
      | byteArray bytes =>
        cases nextRef with
        | valueArray fields => simp [RefRel] at refRel
        | thunk mode value => simp [RefRel] at refRel
        | byteArray nextBytes =>
          have same : bytes = nextBytes := refRel
          subst nextBytes
          cases result : SemanticPrimitivesHOL.xorBytes input bytes with
          | none =>
            exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory, right, result], by
              simp [doApp, applyMemory, left, result, AppResultRel, ResultRel]⟩
          | some updated =>
            have nextStates := stateRel_updateRefFfi source target states ptr
              (.byteArray updated) (.byteArray updated) rfl source.ffi
            refine ⟨.val (unitValue, { target with refs := target.refs.updateEq (ptr, .byteArray updated) }), ?_, ?_⟩
            · simp [doApp, applyMemory, right, result]
            · simp only [doApp, applyMemory, left, bind, Option.bind, result, AppResultRel]
              exact ⟨.block _ [] [] .nil, by simpa [states.2.1] using nextStates⟩

/-- Byte-array XOR preserves the candidate primitive simulation. -/
theorem primitiveSimulation_xorByte {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.memOp .xorByte) := by
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
          | byteVector input => exact xorByte_related source target states flag ptr input
          | _ => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
        | _ => cases second <;>
            exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
      | cons third rest =>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

end Flapjack.Compiler.Backend.ClosAnnotate
