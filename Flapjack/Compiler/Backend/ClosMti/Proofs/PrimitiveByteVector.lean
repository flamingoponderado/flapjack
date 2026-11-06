import Flapjack.Compiler.Backend.ClosMti.Proofs.PrimitiveBlock
import Flapjack.Compiler.Backend.ClosMti.Proofs.PrimitiveArray

/-! Byte-vector operations for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- Related values decode to the same byte-vector sequence. -/
theorem byteVectors_related (maxApp : Nat) {left right : List Value}
    (related : List.Forall₂ (ValueRel maxApp) left right) : byteVectors left = byteVectors right := by
  induction related with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [byteVectors, ih]

/-- Related values decode to the same byte-number sequence. -/
theorem byteNumbers_related (maxApp : Nat) {left right : List Value}
    (related : List.Forall₂ (ValueRel maxApp) left right) : byteNumbers left = byteNumbers right := by
  induction related with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [byteNumbers, ih]

/-- Decoding a closure list into bytes preserves success and malformed input. -/
theorem primitiveSimulation_memory_fromListByte {C F : Type} :
    @PrimitiveSimulation C F (.memOp .fromListByte) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      rename_i value nextValue
      have decoded := ClosProps.valueToList_related (ValueRel source.maxApp)
        (simpleValRel source.maxApp) value nextValue head
      cases l : valueToList value <;> cases r : valueToList nextValue <;>
        simp_all [doApp, applyMemory, excRel]
      have same := byteNumbers_related source.maxApp decoded
      rw [← same]
      cases numbers : byteNumbers _ with
      | none => simp
      | some bytes =>
        have valueRel : ValueRel source.maxApp (.byteVector bytes) (.byteVector bytes) := .byteVector _
        simp [valueRel, states]
    | cons head tail => simp [doApp, applyMemory, excRel]

/-- Concatenating byte vectors preserves byte order and malformed input errors. -/
theorem primitiveSimulation_memory_concatByteVec {C F : Type} :
    @PrimitiveSimulation C F (.memOp .concatByteVec) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      rename_i value nextValue
      have decoded := ClosProps.valueToList_related (ValueRel source.maxApp)
        (simpleValRel source.maxApp) value nextValue head
      cases l : valueToList value <;> cases r : valueToList nextValue <;>
        simp_all [doApp, applyMemory, excRel]
      have same := byteVectors_related source.maxApp decoded
      rw [← same]
      cases vectors : byteVectors _ with
      | none => simp
      | some chunks =>
        have valueRel : ValueRel source.maxApp (.byteVector chunks.flatten) (.byteVector chunks.flatten) := .byteVector _
        simp [valueRel, states]
    | cons head tail => simp [doApp, applyMemory, excRel]

/-- Encoding a byte vector as a closure list preserves every byte. -/
theorem primitiveSimulation_memory_toListByte {C F : Type} :
    @PrimitiveSimulation C F (.memOp .toListByte) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | byteVector bytes =>
        have elements : List.Forall₂ (ValueRel source.maxApp)
            (bytes.map (fun b => .number b.toNat)) (bytes.map (fun b => .number b.toNat)) := by
          induction bytes with
          | nil => exact .nil
          | cons byte rest ih => exact .cons (.number _) ih
        have valueRel := listToValue_related source.maxApp elements
        simp [doApp, applyMemory, valueRel, states]
      | number _ | word64 _ | block _ _ _ _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
        simp [doApp, applyMemory, excRel]
    | cons head tail => simp [doApp, applyMemory, excRel]

/-- Related byte vectors have the same length. -/
theorem primitiveSimulation_memory_lengthByteVec {C F : Type} :
    @PrimitiveSimulation C F (.memOp .lengthByteVec) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | byteVector bytes =>
        have valueRel : ValueRel source.maxApp (.number bytes.length) (.number bytes.length) := .number _
        simp [doApp, applyMemory, valueRel, states]
      | number _ | word64 _ | block _ _ _ _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
        simp [doApp, applyMemory, excRel]
    | cons head tail => simp [doApp, applyMemory, excRel]

/-- Byte-vector indexing preserves both the selected byte and bounds errors. -/
theorem primitiveSimulation_memory_derefByteVec {C F : Type} :
    @PrimitiveSimulation C F (.memOp .derefByteVec) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        cases first with
        | byteVector bytes =>
          cases second with
          | number index =>
            by_cases negative : index < 0
            · simp [doApp, applyMemory, negative, excRel]
            · cases found : bytes[index.toNat]? with
              | none => simp [doApp, applyMemory, negative, found, excRel]
              | some byte =>
                have valueRel : ValueRel source.maxApp (.number byte.toNat) (.number byte.toNat) := .number _
                simp [doApp, applyMemory, negative, found, valueRel, states]
          | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
            simp [doApp, applyMemory, excRel]
        | number _ | word64 _ | block _ _ _ _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
          simp [doApp, applyMemory, excRel]
      | cons head tail => simp [doApp, applyMemory, excRel]

/-- String comparisons return the same Boolean on related byte vectors. -/
theorem primitiveSimulation_memory_stringCmp {C F : Type} (fast : Bool) (op : Opb) :
    @PrimitiveSimulation C F (.memOp (.stringCmp fast op)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        cases first with
        | byteVector left =>
          cases second with
          | byteVector right => simp [doApp, applyMemory, boolValue_related, states]
          | number _ | word64 _ | block _ _ _ _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
            simp [doApp, applyMemory, excRel]
        | number _ | word64 _ | block _ _ _ _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
          simp [doApp, applyMemory, excRel]
      | cons head tail => simp [doApp, applyMemory, excRel]

/-- Array bounds checks observe the same index and related array lengths. -/
theorem primitiveSimulation_memory_boundsCheckArray {C F : Type} :
    @PrimitiveSimulation C F (.memOp .boundsCheckArray) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        cases first with
        | refPtr flag ptr =>
          cases second with
          | number index =>
            have lookup := stateRel_lookupRefs states ptr
            cases l : source.refs.lookup ptr with
            | none => cases r : target.refs.lookup ptr <;> simp_all [optionRel, doApp, applyMemory, excRel]
            | some leftRef =>
              cases r : target.refs.lookup ptr with
              | none => simp_all [optionRel]
              | some rightRef =>
                have refs : RefRel source.maxApp leftRef rightRef := by simpa [optionRel, l, r] using lookup
                cases refs with
                | byteArray bytes => simp [doApp, applyMemory, l, r, excRel]
                | thunk mode value next rel => simp [doApp, applyMemory, l, r, excRel]
                | valueArray fields nextFields rel =>
                  have lengths := rel.length_eq
                  simp [doApp, applyMemory, l, r, ← lengths, boolValue_related, states]
          | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
            simp [doApp, applyMemory, excRel]
        | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure | partialRecclosure =>
          simp [doApp, applyMemory, excRel]
      | cons head tail => simp [doApp, applyMemory, excRel]

/-- Byte bounds checks agree for vectors and mutable arrays. -/
theorem primitiveSimulation_memory_boundsCheckByte {C F : Type} (loose : Bool) :
    @PrimitiveSimulation C F (.memOp (.boundsCheckByte loose)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        cases first with
        | byteVector bytes =>
          cases second with
          | number index => simp [doApp, applyMemory, boolValue_related, states]
          | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
            simp [doApp, applyMemory, excRel]
        | refPtr flag ptr =>
          cases second with
          | number index =>
            have lookup := stateRel_lookupRefs states ptr
            cases l : source.refs.lookup ptr with
            | none => cases r : target.refs.lookup ptr <;> simp_all [optionRel, doApp, applyMemory, excRel]
            | some leftRef =>
              cases r : target.refs.lookup ptr with
              | none => simp_all [optionRel]
              | some rightRef =>
                have refs : RefRel source.maxApp leftRef rightRef := by simpa [optionRel, l, r] using lookup
                cases refs with
                | valueArray fields nextFields rel => simp [doApp, applyMemory, l, r, excRel]
                | thunk mode value next rel => simp [doApp, applyMemory, l, r, excRel]
                | byteArray bytes => simp [doApp, applyMemory, l, r, boolValue_related, states]
          | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
            simp [doApp, applyMemory, excRel]
        | number _ | word64 _ | block _ _ _ _ | closure | recclosure | partialRecclosure =>
          simp [doApp, applyMemory, excRel]
      | cons head tail => simp [doApp, applyMemory, excRel]

/-- GC configuration observes numeric arguments and returns unit. -/
theorem primitiveSimulation_memory_configGC {C F : Type} :
    @PrimitiveSimulation C F (.memOp .configGC) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        cases first <;> cases second <;> simp [doApp, applyMemory, excRel, states, unitValue, ValueRel.block]
      | cons head tail => simp [doApp, applyMemory, excRel]

end Flapjack.Compiler.Backend.ClosMti
