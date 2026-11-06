import Flapjack.Compiler.Backend.Semantics.DataSem.Value

/-! Value and reference projection used by the BVI-to-data simulation. -/
namespace Flapjack.Compiler.Backend.BviToData

/-- Erase data-block timestamps while preserving all other value fields. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_v_def"]
def dataToBviValue : DataSem.Value → BvlSem.Value
  | .number n => .number n
  | .word64 w => .word64 w
  | .block _ tag values => .block tag (values.map dataToBviValue)
  | .codePtr label => .codePtr label
  | .refPtr bit address => .refPtr bit address
termination_by value => sizeOf value

/-- The unit representation is preserved by timestamp erasure. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_v_Unit"]
theorem dataToBviValue_unit : dataToBviValue DataSem.unitValue = BvlSem.unitValue := by
  simp [DataSem.unitValue, BvlSem.unitValue, dataToBviValue]

/-- Boolean representations are preserved by timestamp erasure. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_v_Boolv"]
theorem dataToBviValue_bool (b : Bool) :
    dataToBviValue (DataSem.boolValue b) = BvlSem.boolValue b := by
  simp [DataSem.boolValue, BvlSem.boolValue, dataToBviValue]

/-- Erase timestamps within all value-bearing reference constructors. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_ref_def"]
def dataToBviRef : BvlSem.Ref DataSem.Value → BvlSem.Ref BvlSem.Value
  | .valueArray values => .valueArray (values.map dataToBviValue)
  | .byteArray flag bytes => .byteArray flag bytes
  | .thunk mode value => .thunk mode (dataToBviValue value)
  | .mutBlock tag finished left current right =>
      .mutBlock tag finished (left.map dataToBviValue) (dataToBviValue current) (right.map dataToBviValue)

/-- Decoding a data-language list and then erasing timestamps agrees with
decoding its BVI projection. This is Flapjack proof infrastructure. -/
theorem dataToBviValue_valueToList (value : DataSem.Value) :
    (DataSem.valueToList value).map (List.map dataToBviValue) = BvlSem.valueToList (dataToBviValue value) := by
  cases value with
  | number n => simp [DataSem.valueToList, BvlSem.valueToList, dataToBviValue]
  | word64 w => simp [DataSem.valueToList, BvlSem.valueToList, dataToBviValue]
  | codePtr n => simp [DataSem.valueToList, BvlSem.valueToList, dataToBviValue]
  | refPtr bit n => simp [DataSem.valueToList, BvlSem.valueToList, dataToBviValue]
  | block timestamp tag values =>
    cases values with
    | nil => simp [DataSem.valueToList, BvlSem.valueToList, dataToBviValue]
    | cons head rest =>
      cases rest with
      | nil => simp [DataSem.valueToList, BvlSem.valueToList, dataToBviValue]
      | cons tail rest =>
        cases rest with
        | nil =>
          have ih := dataToBviValue_valueToList tail
          by_cases isCons : tag = BackendCommon.consTag
          · simp only [DataSem.valueToList, BvlSem.valueToList, dataToBviValue,
              List.map_cons, List.map_nil, isCons, ↓reduceIte]
            rw [← ih]
            cases DataSem.valueToList tail <;> rfl
          · simp [DataSem.valueToList, BvlSem.valueToList, dataToBviValue, isCons]
        | cons third rest => simp [DataSem.valueToList, BvlSem.valueToList, dataToBviValue]
termination_by sizeOf value

end Flapjack.Compiler.Backend.BviToData
