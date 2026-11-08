import Flapjack.SemanticPrimitivesHOL

/-! Maps over semantic results and their exception payloads. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.SemanticPrimitivesHOL

/-- Map exception values while leaving abort reasons unchanged. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "map_error_result_def"]
def mapErrorResult {α β : Type} (f : α → β) : ErrorResult α → ErrorResult β
  | .raise value => .raise (f value)
  | .abort reason => .abort reason

/-- Mapping exception payloads cannot create or change an abort. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "map_error_result_Rtype_error"]
theorem mapErrorResult_abort {α β : Type} (f : α → β) (error : ErrorResult α) (reason : Abort) :
    mapErrorResult f error = .abort reason ↔ error = .abort reason := by
  cases error <;> simp [mapErrorResult]

/-- Mapping the identity function leaves an error result unchanged. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "map_error_result_I"]
theorem mapErrorResult_id {α : Type} (error : ErrorResult α) : mapErrorResult id error = error := by
  cases error <;> rfl

/-- Map successful results and exception values independently. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "map_result_def"]
def mapResult {α β γ δ : Type} (f : α → γ) (g : β → δ) : Result α β → Result γ δ
  | .val value => .val (f value)
  | .err error => .err (mapErrorResult g error)

/-- A mapped successful result comes from a successful input. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "map_result_Rval"]
theorem mapResult_val {α β γ δ : Type} (f : α → γ) (g : β → δ)
    (result : Result α β) (value : γ) :
    mapResult f g result = .val value ↔ ∃ input, result = .val input ∧ value = f input := by
  cases result <;> simp [mapResult, eq_comm]

/-- A mapped error comes from an error input with the mapped payload. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "map_result_Rerr"]
theorem mapResult_err {α β γ δ : Type} (f : α → γ) (g : β → δ)
    (result : Result α β) (error : ErrorResult δ) :
    mapResult f g result = .err error ↔ ∃ input, result = .err input ∧ mapErrorResult g input = error := by
  cases result <;> simp [mapResult]

end Flapjack.SemanticPrimitivesProps
