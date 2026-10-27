import Flapjack.Compiler.Backend.Semantics.FlatSem
import Flapjack.Compiler.Backend.BackendCommon.ConstructorTags
import Flapjack.Basis.Pure.MlString

/-! List and string conversions used by the flat-language evaluator. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.BackendCommon

/-- Decode the original flat list constructors, rejecting malformed values. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "v_to_list_def"]
def valueToList : Value → Option (List Value)
  | .conv (some (cid, tid)) [] =>
    if cid = nilTag ∧ tid = some listId then some [] else none
  | .conv (some (cid, tid)) [head, tail] =>
    if cid = consTag ∧ tid = some listId then
      (valueToList tail).map (head :: ·)
    else none
  | _ => none
termination_by value => sizeOf value

/-- Encode a list with the original flat list constructors. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "list_to_v_def"]
def listToValue : List Value → Value
  | [] => .conv (some (nilTag, some listId)) []
  | head :: tail => .conv (some (consTag, some listId)) [head, listToValue tail]

/-- Decode a flat list whose elements are character literals. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "v_to_char_list_def"]
def valueToCharList : Value → Option (List HolChar)
  | .conv (some (cid, tid)) [] =>
    if cid = nilTag ∧ tid = some listId then some [] else none
  | .conv (some (cid, tid)) [.litv (.char head), tail] =>
    if cid = consTag ∧ tid = some listId then
      (valueToCharList tail).map (head :: ·)
    else none
  | _ => none
termination_by value => sizeOf value

/-- Concatenate a list of string literals, rejecting any other value. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "vs_to_string_def"]
def valuesToString : List Value → Option MlString
  | [] => some (ofString "")
  | .litv (.strLit head) :: tail => (valuesToString tail).map (fun rest => MlString.concat [head, rest])
  | _ => none

end Flapjack.Compiler.Backend.FlatSem
