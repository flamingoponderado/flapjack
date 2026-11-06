import Flapjack.Compiler.Backend.ClosMti.Proofs.PrimitiveGlobal

/-! Array operations for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- Value-array length agrees on related stores, including invalid references. -/
theorem primitiveSimulation_memory_length {C F : Type} :
    @PrimitiveSimulation C F (.memOp .length) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | refPtr flag index =>
        have lookup := stateRel_lookupRefs states index
        cases l : source.refs.lookup index with
        | none => cases r : target.refs.lookup index <;> simp_all [OptionRel, doApp, applyMemory, excRel]
        | some leftRef =>
          cases r : target.refs.lookup index with
          | none => simp_all [OptionRel]
          | some rightRef =>
            have refs : RefRel source.maxApp leftRef rightRef := by simpa [OptionRel, l, r] using lookup
            cases refs with
            | byteArray bytes => simp [doApp, applyMemory, l, r, excRel]
            | thunk mode value next rel => simp [doApp, applyMemory, l, r, excRel]
            | valueArray fields nextFields rel =>
              have lengths := rel.length_eq
              have resultRel : ValueRel source.maxApp (.number fields.length) (.number fields.length) := .number _
              simp [doApp, applyMemory, l, r, ← lengths, resultRel, states]
      | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure | partialRecclosure =>
        simp [doApp, applyMemory, excRel]
    | cons head tail => simp [doApp, applyMemory, excRel]

/-- Byte-array length agrees on related stores, including invalid references. -/
theorem primitiveSimulation_memory_lengthByte {C F : Type} :
    @PrimitiveSimulation C F (.memOp .lengthByte) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | refPtr flag index =>
        have lookup := stateRel_lookupRefs states index
        cases l : source.refs.lookup index with
        | none => cases r : target.refs.lookup index <;> simp_all [OptionRel, doApp, applyMemory, excRel]
        | some leftRef =>
          cases r : target.refs.lookup index with
          | none => simp_all [OptionRel]
          | some rightRef =>
            have refs : RefRel source.maxApp leftRef rightRef := by simpa [OptionRel, l, r] using lookup
            cases refs with
            | valueArray fields nextFields rel => simp [doApp, applyMemory, l, r, excRel]
            | thunk mode value next rel => simp [doApp, applyMemory, l, r, excRel]
            | byteArray bytes =>
              have valueRel : ValueRel source.maxApp (.number bytes.length) (.number bytes.length) := .number _
              simp [doApp, applyMemory, l, r, valueRel, states]
      | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure | partialRecclosure =>
        simp [doApp, applyMemory, excRel]
    | cons head tail => simp [doApp, applyMemory, excRel]

/-- Indexed reads preserve corresponding values and reject the same bad
indices, whether the input is a block or a reference to a value array. -/
theorem primitiveSimulation_memory_el {C F : Type} :
    @PrimitiveSimulation C F (.memOp .el) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        cases second with
        | number index =>
          cases first with
          | block tag fields nextFields fieldsRel =>
            by_cases negative : index < 0
            · simp [doApp, applyMemory, negative, excRel]
            · have lookupRel := forall₂_getElemRel fieldsRel index.toNat
              cases l : fields[index.toNat]? <;> cases r : nextFields[index.toNat]? <;>
                simp_all [OptionRel, doApp, applyMemory, excRel]
              simp [show ¬ index < 0 by omega, lookupRel, states]
          | refPtr flag ptr =>
            have lookup := stateRel_lookupRefs states ptr
            cases l : source.refs.lookup ptr with
            | none => cases r : target.refs.lookup ptr <;> simp_all [OptionRel, doApp, applyMemory, excRel]
            | some leftRef =>
              cases r : target.refs.lookup ptr with
              | none => simp_all [OptionRel]
              | some rightRef =>
                have refs : RefRel source.maxApp leftRef rightRef := by simpa [OptionRel, l, r] using lookup
                cases refs with
                | byteArray bytes => simp [doApp, applyMemory, l, r, excRel]
                | thunk mode value next rel => simp [doApp, applyMemory, l, r, excRel]
                | valueArray fields nextFields rel =>
                  by_cases negative : index < 0
                  · simp [doApp, applyMemory, l, r, negative, excRel]
                  · have lookupRel := forall₂_getElemRel rel index.toNat
                    cases sourceValue : fields[index.toNat]? <;> cases targetValue : nextFields[index.toNat]? <;>
                      simp_all [OptionRel, doApp, applyMemory, excRel]
                    simp [show ¬ index < 0 by omega, lookupRel, states]
          | number _ | word64 _ | byteVector _ | closure | recclosure | partialRecclosure =>
            simp [doApp, applyMemory, excRel]
        | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
          cases first <;> simp [doApp, applyMemory, excRel]
      | cons head tail => simp [doApp, applyMemory, excRel]

/-- Updating a value-array element preserves related contents and rejects the
same bad references and indices. -/
theorem primitiveSimulation_memory_update {C F : Type} :
    @PrimitiveSimulation C F (.memOp .update) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | cons second tail =>
      cases tail with
      | nil => simp [doApp, applyMemory, excRel]
      | cons third tail =>
        cases tail with
        | nil =>
          cases first with
          | refPtr flag ptr =>
            cases second with
            | number index =>
              rename_i value nextValue
              have lookup := stateRel_lookupRefs states ptr
              cases l : source.refs.lookup ptr with
              | none => cases r : target.refs.lookup ptr <;> simp_all [OptionRel, doApp, applyMemory, excRel]
              | some leftRef =>
                cases r : target.refs.lookup ptr with
                | none => simp_all [OptionRel]
                | some rightRef =>
                  have refs : RefRel source.maxApp leftRef rightRef := by simpa [OptionRel, l, r] using lookup
                  cases refs with
                  | byteArray bytes => simp [doApp, applyMemory, l, r, excRel]
                  | thunk mode value next rel => simp [doApp, applyMemory, l, r, excRel]
                  | valueArray fields nextFields rel =>
                    have lengths := rel.length_eq
                    by_cases invalid : index < 0 ∨ index.toNat ≥ fields.length
                    · simp [doApp, applyMemory, l, r, ← lengths, invalid, excRel]
                    · have fieldsUpdated := forall₂_set rel index.toNat value nextValue third
                      have updated := stateRel_updateRefs states ptr (.valueArray (fields.set index.toNat value))
                        (.valueArray (nextFields.set index.toNat nextValue)) (.valueArray _ _ fieldsUpdated)
                      have unitRel : ValueRel source.maxApp unitValue unitValue := .block _ [] [] .nil
                      simp [doApp, applyMemory, l, r, ← lengths, invalid, unitRel, updated]
            | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
              simp [doApp, applyMemory, excRel]
          | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure | partialRecclosure =>
            cases second <;> simp [doApp, applyMemory, excRel]
        | cons head tail => simp [doApp, applyMemory, excRel]

/-- Byte-array reads agree on bounds and return the same byte. -/
theorem primitiveSimulation_memory_derefByte {C F : Type} :
    @PrimitiveSimulation C F (.memOp .derefByte) := by
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
            | none => cases r : target.refs.lookup ptr <;> simp_all [OptionRel, doApp, applyMemory, excRel]
            | some leftRef =>
              cases r : target.refs.lookup ptr with
              | none => simp_all [OptionRel]
              | some rightRef =>
                have refs : RefRel source.maxApp leftRef rightRef := by simpa [OptionRel, l, r] using lookup
                cases refs with
                | valueArray fields nextFields rel => simp [doApp, applyMemory, l, r, excRel]
                | thunk mode value next rel => simp [doApp, applyMemory, l, r, excRel]
                | byteArray bytes =>
                  by_cases negative : index < 0
                  · simp [doApp, applyMemory, l, r, negative, excRel]
                  · cases found : bytes[index.toNat]? with
                    | none => simp [doApp, applyMemory, l, r, negative, found, excRel]
                    | some byte =>
                      have valueRel : ValueRel source.maxApp (.number byte.toNat) (.number byte.toNat) := .number _
                      simp [doApp, applyMemory, l, r, negative, found, valueRel, states]
          | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
            simp [doApp, applyMemory, excRel]
        | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure | partialRecclosure =>
          cases second <;> simp [doApp, applyMemory, excRel]
      | cons head tail => simp [doApp, applyMemory, excRel]

/-- Byte-array writes agree on bounds and update both stores identically. -/
theorem primitiveSimulation_memory_updateByte {C F : Type} :
    @PrimitiveSimulation C F (.memOp .updateByte) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | cons second tail =>
      cases tail with
      | nil => simp [doApp, applyMemory, excRel]
      | cons third tail =>
        cases tail with
        | nil =>
          cases first with
          | refPtr flag ptr =>
            cases second with
            | number index =>
              cases third with
              | number byte =>
                have lookup := stateRel_lookupRefs states ptr
                cases l : source.refs.lookup ptr with
                | none => cases r : target.refs.lookup ptr <;> simp_all [OptionRel, doApp, applyMemory, excRel]
                | some leftRef =>
                  cases r : target.refs.lookup ptr with
                  | none => simp_all [OptionRel]
                  | some rightRef =>
                    have refs : RefRel source.maxApp leftRef rightRef := by simpa [OptionRel, l, r] using lookup
                    cases refs with
                    | valueArray fields nextFields rel => simp [doApp, applyMemory, l, r, excRel]
                    | thunk mode value next rel => simp [doApp, applyMemory, l, r, excRel]
                    | byteArray bytes =>
                      by_cases invalid : index < 0 ∨ index.toNat ≥ bytes.length
                      · simp [doApp, applyMemory, l, r, invalid, excRel]
                      · cases converted : intToByte byte with
                        | none => simp [doApp, applyMemory, l, r, invalid, converted, excRel]
                        | some value =>
                          have updated := stateRel_updateRefs states ptr (.byteArray (bytes.set index.toNat value))
                            (.byteArray (bytes.set index.toNat value)) (.byteArray _)
                          have unitRel : ValueRel source.maxApp unitValue unitValue := .block _ [] [] .nil
                          simp [doApp, applyMemory, l, r, invalid, converted, unitRel, updated]
              | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
                simp [doApp, applyMemory, excRel]
            | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
              simp [doApp, applyMemory, excRel]
          | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure | partialRecclosure =>
            cases second <;> simp [doApp, applyMemory, excRel]
        | cons head tail => simp [doApp, applyMemory, excRel]

end Flapjack.Compiler.Backend.ClosMti
