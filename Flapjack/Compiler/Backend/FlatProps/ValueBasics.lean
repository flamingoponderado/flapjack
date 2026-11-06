import Flapjack.Compiler.Backend.Semantics.FlatSem

/-! Basic flat values and their recursively contained values. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem

/-- A closure value is either a single or recursive closure. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "isClosure_def"]
def isClosure (value : Value) : Prop :=
  (∃ env name body, value = .closure env name body) ∨
    ∃ env functions name, value = .recclosure env functions name

@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_basic_val_rel_def"]
def simpleBasicValRel : Value → Value → Prop
  | .litv lit, value => value = .litv lit
  | .loc flag index, value => value = .loc flag index
  | .conv stamp _, value => ∃ values, value = .conv stamp values
  | .vectorv _, value => ∃ values, value = .vectorv values
  | .closure _ _ _, _ | .recclosure _ _ _, _ => False

@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "v_container_xs_def"]
def valueContainerXs : Value → List Value
  | .conv _ values | .vectorv values => values
  | _ => []

end Flapjack.Compiler.Backend.FlatProps
