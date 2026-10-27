import Flapjack.SemanticPrimitivesHOL

/-! Source value encodings used by evaluator primitives. Statement review is pending. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "list_type_num_def"]
def listTypeNum : Nat := 1
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "option_type_num_def"]
def optionTypeNum : Nat := 2
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "id_type_num_def"]
def idTypeNum : Nat := 4

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "v_to_list_def"]
def valueToList : Value → Option (List Value)
  | .conv (some stamp) [] =>
    if stamp = .typeStamp (ofString "[]") listTypeNum then some [] else none
  | .conv (some stamp) [head, tail] =>
    if stamp = .typeStamp (ofString "::") listTypeNum then
      (valueToList tail).map (head :: ·)
    else none
  | _ => none
termination_by value => sizeOf value

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "list_to_v_def"]
def listToValue : List Value → Value
  | [] => .conv (some (.typeStamp (ofString "[]") listTypeNum)) []
  | head :: tail => .conv (some (.typeStamp (ofString "::") listTypeNum)) [head, listToValue tail]

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "v_to_char_list_def"]
def valueToCharList : Value → Option (List HolChar)
  | .conv (some stamp) [] =>
    if stamp = .typeStamp (ofString "[]") listTypeNum then some [] else none
  | .conv (some stamp) [.litv (.char head), tail] =>
    if stamp = .typeStamp (ofString "::") listTypeNum then
      (valueToCharList tail).map (head :: ·)
    else none
  | _ => none
termination_by value => sizeOf value

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "vs_to_string_def"]
def valuesToString : List Value → Option MlString
  | [] => some (ofString "")
  | .litv (.strLit head) :: tail => (valuesToString tail).map (fun rest => MlString.concat [head, rest])
  | _ => none

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "maybe_to_v_def"]
def maybeToValue : Option Value → Value
  | none => .conv (some (.typeStamp (ofString "None") optionTypeNum)) []
  | some value => .conv (some (.typeStamp (ofString "Some") optionTypeNum)) [value]

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "v_to_id_def"]
def valueToId : Value → Option (Ident ModN VarN)
  | .conv (some stamp) [.litv (.strLit name)] =>
    if stamp = .typeStamp (ofString "Short") idTypeNum then some (.short name) else none
  | .conv (some stamp) [.litv (.strLit name), tail] =>
    if stamp = .typeStamp (ofString "Long") idTypeNum then (valueToId tail).map (.long name ·) else none
  | _ => none
termination_by value => sizeOf value

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "nat_to_v_def"]
def natToValue (n : Nat) : Value := .litv (.intLit (Int.ofNat n))

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "maybe_all_list_def"]
def maybeAllList {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some head :: tail => (maybeAllList tail).map (head :: ·)

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "v_to_word8_def"]
def valueToWord8 : Value → Option (BitVec 8)
  | .litv (.word8 word) => some word
  | _ => none

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "v_to_word64_def"]
def valueToWord64 : Value → Option (BitVec 64)
  | .litv (.word64 word) => some word
  | _ => none

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "v_to_word8_list_def"]
def valueToWord8List (value : Value) : Option (List (BitVec 8)) := do
  let values ← valueToList value
  maybeAllList (values.map valueToWord8)

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "v_to_word64_list_def"]
def valueToWord64List (value : Value) : Option (List (BitVec 64)) := do
  let values ← valueToList value
  maybeAllList (values.map valueToWord64)

end Flapjack.SemanticPrimitivesHOL
