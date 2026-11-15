module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Value

@[expose] public section

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

/-- Decoding a BVI projection agrees with decoding the DATA value and then
erasing timestamps. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "v_to_list_eq"]
theorem dataToBviValue_valueToList (value : DataSem.Value) :
    BvlSem.valueToList (dataToBviValue value) = (DataSem.valueToList value).map (List.map dataToBviValue) := by
  symm
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
          have ih := (dataToBviValue_valueToList tail).symm
          by_cases isCons : tag = BackendCommon.consTag
          · simp only [DataSem.valueToList, BvlSem.valueToList, dataToBviValue,
              List.map_cons, List.map_nil, isCons, ↓reduceIte]
            rw [← ih]
            cases DataSem.valueToList tail <;> rfl
          · simp [DataSem.valueToList, BvlSem.valueToList, dataToBviValue, isCons]
        | cons third rest => simp [DataSem.valueToList, BvlSem.valueToList, dataToBviValue]
termination_by sizeOf value

end Flapjack.Compiler.Backend.BviToData
