module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.ByteReads
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.BlockLists

@[expose] public section

/-! Byte-list conversions under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Related numeric lists decode to exactly the same byte sequence. -/
theorem byteNumbers_related (left right : List Value) (related : List.Forall₂ ValueRel left right) :
    byteNumbers left = byteNumbers right := by
  induction related with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [byteNumbers, ih]

/-- Related byte-vector lists decode to exactly the same sequence of chunks. -/
theorem byteVectors_related (left right : List Value) (related : List.Forall₂ ValueRel left right) :
    byteVectors left = byteVectors right := by
  induction related with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [byteVectors, ih]

/-- Decode either individual byte values or a list of byte-vector chunks. -/
def decodedBytes (chunks : Bool) (value : Value) : Option (List (BitVec 8)) := do
  let values ← valueToList value
  if chunks then (byteVectors values).map List.flatten else byteNumbers values

/-- Related encoded lists produce identical decoded bytes, or both fail. -/
theorem decodedBytes_related (chunks : Bool) (left right : Value) (related : ValueRel left right) :
    decodedBytes chunks left = decodedBytes chunks right := by
  have decoded := valueToList_related left right related
  cases leftRun : valueToList left with
  | none =>
    cases rightRun : valueToList right <;> simp_all [decodedBytes, optionRel]
  | some xs =>
    cases rightRun : valueToList right with
    | none => simp [leftRun, rightRun, optionRel] at decoded
    | some ys =>
      have listRel : List.Forall₂ ValueRel xs ys := by simpa [leftRun, rightRun, optionRel] using decoded
      have numbers := byteNumbers_related xs ys listRel
      have vectors := byteVectors_related xs ys listRel
      simp [decodedBytes, leftRun, rightRun, numbers, vectors]

/-- The byte conversion dispatcher produces the decoded bytes as a vector. -/
theorem applyMemory_decodedBytes {C F : Type} (chunks : Bool) (value : Value) (state : State C F) :
    applyMemory (if chunks then .concatByteVec else .fromListByte) [value] state =
      (decodedBytes chunks value).map (fun bytes => (.byteVector bytes, state)) := by
  cases chunks <;> cases h : valueToList value with
  | none => simp [applyMemory, decodedBytes, h]
  | some values =>
    all_goals cases hNum : byteNumbers values <;> cases hVec : byteVectors values <;>
      simp [applyMemory, decodedBytes, h, hNum, hVec]

/-- Decoding byte lists and concatenating vector lists preserve simulation. -/
theorem primitiveSimulation_decodedBytes {C F : Type} (chunks : Bool) :
    PrimitiveSimulation (C := C) (F := F) (.memOp (if chunks then .concatByteVec else .fromListByte)) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => cases chunks <;> exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons head tail =>
    cases tail with
    | nil =>
      rename_i value nextValue
      have same := decodedBytes_related chunks value nextValue head
      cases decoded : decodedBytes chunks value with
      | none =>
        have nextDecoded : decodedBytes chunks nextValue = none := by rw [← same, decoded]
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory_decodedBytes, nextDecoded], by
          simp [doApp, applyMemory_decodedBytes, decoded, AppResultRel, ResultRel]⟩
      | some bytes =>
        have nextDecoded : decodedBytes chunks nextValue = some bytes := by rw [← same, decoded]
        refine ⟨.val (.byteVector bytes, target), ?_, ?_⟩
        · simp [doApp, applyMemory_decodedBytes, nextDecoded]
        · simp only [doApp, applyMemory_decodedBytes, decoded, AppResultRel]
          exact ⟨.byteVector bytes, states⟩
    | cons first rest => cases chunks <;>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

/-- A byte vector converts to a related encoded list of byte numbers. -/
theorem primitiveSimulation_toListByte {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.memOp .toListByte) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | byteVector bytes =>
        have numbers : List.Forall₂ ValueRel (bytes.map (fun b => .number b.toNat))
            (bytes.map (fun b => .number b.toNat)) := by
          rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
          intro byte member
          exact .number _
        refine ⟨.val (listToValue (bytes.map (fun b => .number b.toNat)), target), ?_, ?_⟩
        · simp [doApp, applyMemory]
        · simp only [doApp, applyMemory, AppResultRel]
          exact ⟨listToValue_related _ _ numbers, states⟩
      | _ => exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons first rest =>
      exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

end Flapjack.Compiler.Backend.ClosAnnotate
