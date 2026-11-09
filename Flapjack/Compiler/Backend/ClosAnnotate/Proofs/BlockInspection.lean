import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.GlobalOperations

/-! Constructor inspection under the closure-annotation relation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Lift related optional values to related state-preserving primitive results. -/
theorem pureOption_result {C F : Type} (left right : Option Value) (source target : State C F)
    (valuesRel : optionRel ValueRel left right) (states : StateRel source target) :
    ∃ outcome,
      (match right.map (fun value => (value, target)) with
       | none => .err (.abort .typeError) | some pair => .val pair) = outcome ∧
      AppResultRel
        (match left.map (fun value => (value, source)) with
         | none => .err (.abort .typeError) | some pair => .val pair) outcome := by
  cases left with
  | none =>
    cases right with
    | none => exact ⟨.err (.abort .typeError), rfl, rfl⟩
    | some value => contradiction
  | some value =>
    cases right with
    | none => contradiction
    | some nextValue => exact ⟨.val (nextValue, target), rfl, ⟨valuesRel, states⟩⟩

/-- A unary block primitive is simulated when it maps related field lists to
related optional values and rejects all other argument shapes. -/
theorem primitiveSimulation_unaryBlock {C F : Type} (op : ClosLang.BlockOp)
    (inspect : Nat → List Value → Option Value)
    (equation : ∀ (args : List Value) (state : State C F), applyBlock op args state =
      match args with
      | [.block tag fields] => (inspect tag fields).map (fun value => (value, state))
      | _ => none)
    (preserves : ∀ tag fields nextFields, List.Forall₂ ValueRel fields nextFields →
      optionRel ValueRel (inspect tag fields) (inspect tag nextFields)) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp op) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp, equation], by simp [doApp, equation, AppResultRel, ResultRel]⟩
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | block tag fields nextFields fieldsRel =>
        obtain ⟨outcome, nextRun, rel⟩ := pureOption_result (inspect tag fields) (inspect tag nextFields)
          source target (preserves tag fields nextFields fieldsRel) states
        refine ⟨outcome, ?_, ?_⟩
        · cases h : inspect tag nextFields <;> simpa [doApp, equation, h] using nextRun
        · cases h : inspect tag fields <;> simpa [doApp, equation, h] using rel
      | _ => exact ⟨.err (.abort .typeError), by simp [doApp, equation], by simp [doApp, equation, AppResultRel, ResultRel]⟩
    | cons first rest =>
      exact ⟨.err (.abort .typeError), by simp [doApp, equation], by simp [doApp, equation, AppResultRel, ResultRel]⟩

/-- Selecting a block field preserves related values and bounds failures. -/
theorem primitiveSimulation_elemAt {C F : Type} (index : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.elemAt index)) := by
  apply primitiveSimulation_unaryBlock (.elemAt index) (fun _ fields => fields[index]?)
  · intro args state
    cases args with
    | nil => rfl
    | cons first rest => cases rest with
      | nil => cases first <;> simp [applyBlock, Option.map_eq_bind]
      | cons second rest => cases first <;> rfl
  · intro tag fields nextFields related
    exact optionRel_getElem fields nextFields related index

/-- Reading a block's tag preserves the primitive relation. -/
theorem primitiveSimulation_tagEq {C F : Type} (tag : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.tagEq tag)) := by
  apply primitiveSimulation_unaryBlock (.tagEq tag) (fun actual _ => some (boolValue (actual == tag)))
  · intro args state
    cases args with
    | nil => rfl
    | cons first rest => cases rest with
      | nil => cases first <;> rfl
      | cons second rest => cases first <;> rfl
  · intro actual fields nextFields related
    exact .block _ [] [] .nil

/-- Reading a block's length preserves the primitive relation. -/
theorem primitiveSimulation_lengthBlock {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.blockOp .lengthBlock) := by
  apply primitiveSimulation_unaryBlock .lengthBlock (fun _ fields => some (.number fields.length))
  · intro args state
    cases args with
    | nil => rfl
    | cons first rest => cases rest with
      | nil => cases first <;> rfl
      | cons second rest => cases first <;> rfl
  · intro actual fields nextFields related
    change ValueRel (.number fields.length) (.number nextFields.length)
    rw [related.length_eq]
    exact .number _

/-- Comparing a block's length preserves the primitive relation. -/
theorem primitiveSimulation_lenEq {C F : Type} (length : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.lenEq length)) := by
  apply primitiveSimulation_unaryBlock (.lenEq length) (fun _ fields => some (boolValue (fields.length == length)))
  · intro args state
    cases args with
    | nil => rfl
    | cons first rest => cases rest with
      | nil => cases first <;> rfl
      | cons second rest => cases first <;> rfl
  · intro actual fields nextFields related
    change ValueRel (boolValue (fields.length == length)) (boolValue (nextFields.length == length))
    rw [related.length_eq]
    exact .block _ [] [] .nil

/-- Comparing a block's tag and length preserves the primitive relation. -/
theorem primitiveSimulation_tagLenEq {C F : Type} (tag length : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.tagLenEq tag length)) := by
  apply primitiveSimulation_unaryBlock (.tagLenEq tag length)
    (fun actual fields => some (boolValue (actual == tag && fields.length == length)))
  · intro args state
    cases args with
    | nil => rfl
    | cons first rest => cases rest with
      | nil => cases first <;> rfl
      | cons second rest => cases first <;> rfl
  · intro actual fields nextFields related
    change ValueRel (boolValue (actual == tag && fields.length == length))
      (boolValue (actual == tag && nextFields.length == length))
    rw [related.length_eq]
    exact .block _ [] [] .nil

end Flapjack.Compiler.Backend.ClosAnnotate
