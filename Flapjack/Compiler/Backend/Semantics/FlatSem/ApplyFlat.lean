import Flapjack.Compiler.Backend.Semantics.FlatSem

/-! Flat-specific primitive operations. The complete `do_app` also includes
source operations and is not yet assembled. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL

/-- Flat-specific cases of primitive application. An outer `none` means the
operation belongs to the source-operation dispatcher; `some none` is the
original type-error result for a supported flat operation. This partial
dispatcher has no HOL attribute because it is not the complete `do_app`. -/
def doAppFlat {C F : Type} (state : State C F) (op : FlatLang.Op) (values : List Value) :
    Option (Option (State C F × Result Value Value)) :=
  match op with
  | .src _ => none
  | .globalVarAlloc n => some <| match values with
    | [] => some ({ state with globals := state.globals ++ List.replicate n none }, .val unitValue)
    | _ => none
  | .globalVarInit n => some <| match values, state.globals[n]? with
    | [value], some none => some ({ state with globals := state.globals.set n (some value) }, .val unitValue)
    | _, _ => none
  | .globalVarLookup n => some <| match values, state.globals[n]? with
    | [], some (some value) => some (state, .val value)
    | _, _ => none
  | .tagLenEq tag length => some <| match values with
    | [.conv (some (actual, _)) fields] => some (state, .val (boolValue (actual == tag && fields.length == length)))
    | _ => none
  | .lenEq length => some <| match values with
    | [.conv _ fields] => some (state, .val (boolValue (fields.length == length)))
    | _ => none
  | .el n => some <| match values with
    | [.conv _ fields] => (fields[n]?).map fun value => (state, .val value)
    | [.loc _ index] =>
      if n = 0 then match storeLookup index state.refs with
        | some (.refv value) => some (state, .val value)
        | _ => none
      else none
    | _ => none
  | .id => some <| match values with
    | [value] => some (state, .val value)
    | _ => none

end Flapjack.Compiler.Backend.FlatSem
