module

public import Flapjack.SemanticPrimitivesHOL

@[expose] public section

/-! Values carried by flat reference-store entries. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.SemanticPrimitivesHOL (StoreValue)

/-- Collect the values directly contained in a store entry. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "store_v_vs_def"]
def storeValueValues {α : Type} : StoreValue α → List α
  | .varray values => values
  | .refv value => [value]
  | .thunk _ value => [value]
  | .w8array _ => []

end Flapjack.Compiler.Backend.FlatProps
