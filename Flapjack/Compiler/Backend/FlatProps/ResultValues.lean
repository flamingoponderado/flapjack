import Flapjack.Compiler.Backend.Semantics.FlatSem

/-! Values exposed by a flat evaluator result. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.SemanticPrimitivesHOL

/-- Values returned or raised by a flat evaluation result. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "result_vs_def"]
def resultValues {α : Type} : Result (List α) α → List α
  | .val values => values
  | .err (.raise value) => [value]
  | .err (.abort _) => []

end Flapjack.Compiler.Backend.FlatProps
