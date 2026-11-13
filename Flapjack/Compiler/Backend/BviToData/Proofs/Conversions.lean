module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Value
public import Flapjack.Compiler.Backend.Semantics.DataSem.Conversions

@[expose] public section

/-! Installation decoder preservation under timestamp erasure. -/
namespace Flapjack.Compiler.Backend.BviToData

private theorem byteNumbers_projection (values : List DataSem.Value) :
    BvlSem.byteNumbers (values.map dataToBviValue) = DataSem.byteNumbers values := by
  induction values with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [dataToBviValue, BvlSem.byteNumbers, DataSem.byteNumbers, ih]

private theorem wordValues_projection (values : List DataSem.Value) :
    BvlSem.wordValues (values.map dataToBviValue) = DataSem.wordValues values := by
  induction values with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [dataToBviValue, BvlSem.wordValues, DataSem.wordValues, ih]

/-- Decoding bytes commutes with erasing timestamps. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "v_to_bytes_eq"]
theorem valueToBytes_projection (value : DataSem.Value) :
    BvlSem.valueToBytes (dataToBviValue value) = DataSem.valueToBytes value := by
  simp only [BvlSem.valueToBytes, DataSem.valueToBytes, dataToBviValue_valueToList]
  cases DataSem.valueToList value with
  | none => rfl
  | some values => simpa using byteNumbers_projection values

/-- Decoding words commutes with erasing timestamps. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "v_to_words_eq"]
theorem valueToWords_projection (value : DataSem.Value) :
    BvlSem.valueToWords (dataToBviValue value) = DataSem.valueToWords value := by
  simp only [BvlSem.valueToWords, DataSem.valueToWords, dataToBviValue_valueToList]
  cases DataSem.valueToList value with
  | none => rfl
  | some values => simpa using wordValues_projection values

end Flapjack.Compiler.Backend.BviToData
