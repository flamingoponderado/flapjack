module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Value
public import Flapjack.Compiler.Backend.Semantics.BviSem.State

@[expose] public section

/-! Result projection for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Project data results, distinguishing exceptions from BVI returns. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_result_def"]
def dataToBviResult : Result (List DataSem.Value) DataSem.Value → BviSem.BviResult
  | .val values => .val (values.map dataToBviValue)
  | .err (.raise value) => .err (.raise (.exn (dataToBviValue value)))
  | .err (.abort error) => .err (.abort error)

/-- A projected data result is a BVI raise exactly when the data result is a
raise whose value projects to that BVI exception. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_result_eq"]
theorem dataToBviResult_eq (result : Result (List DataSem.Value) DataSem.Value)
    (value : BviSem.ExnOrRet) :
    dataToBviResult result = .err (.raise value) ↔
      ∃ dataValue, result = .err (.raise dataValue) ∧ .exn (dataToBviValue dataValue) = value := by
  cases result with
  | val values => simp [dataToBviResult]
  | err error => cases error <;> simp [dataToBviResult]

end Flapjack.Compiler.Backend.BviToData
