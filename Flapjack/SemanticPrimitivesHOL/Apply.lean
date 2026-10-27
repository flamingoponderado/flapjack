import Flapjack.SemanticPrimitivesHOL.Primitives
import Flapjack.SemanticPrimitivesHOL.Conversions
import Flapjack.SemanticPrimitivesHOL.Operations

/-! Initial source primitive application cases. This is Flapjack infrastructure
for assembling the source evaluator, not a port of the complete HOL `do_app`:
outer `none` means an operation is not implemented, while `some none` means
HOL's type-error result for a supported operation. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL

abbrev BasicAppResult (σ : Type) :=
  (Store Value × HolFfiState σ) × Result Value Value

/-- Supported pure, reference and list cases of source primitive application.
The complete HOL `do_app` has additional cases and no outer unsupported result;
this partial dispatcher therefore intentionally has no `@[hol]` attribute. -/
def doAppBasic {σ : Type} (state : Store Value × HolFfiState σ) (op : Op)
    (values : List Value) : Option (Option (BasicAppResult σ)) :=
  let (store, ffi) := state
  match op with
  | .listAppend => some do
    match values with
    | [first, second] =>
      let left ← valueToList first
      let right ← valueToList second
      some (state, .val (listToValue (left ++ right)))
    | _ => none
  | .shift .w8 shift amount => some <| match values with
    | [.litv (.word8 word)] => some (state, .val (.litv (.word8 (shift8Lookup shift word amount))))
    | _ => none
  | .shift .w64 shift amount => some <| match values with
    | [.litv (.word64 word)] => some (state, .val (.litv (.word64 (shift64Lookup shift word amount))))
    | _ => none
  | .equality => some <| match values with
    | [first, second] => match doEq first second with
      | .typeError => none
      | .val b => some (state, .val (boolValue b))
    | _ => none
  | .opassign => some do
    match values with
    | [.loc _ address, value] =>
      let store ← storeAssign address (.refv value) store
      some ((store, ffi), .val (.conv none []))
    | _ => none
  | .opref => some <| match values with
    | [value] =>
      let (store, address) := storeAlloc (.refv value) store
      some ((store, ffi), .val (.loc true address))
    | _ => none
  | .opderef => some <| match values with
    | [.loc _ address] => match storeLookup address store with
      | some (.refv value) => some (state, .val value)
      | _ => none
    | _ => none
  | _ => none

end Flapjack.SemanticPrimitivesHOL
