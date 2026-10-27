import Flapjack.Compiler.Inference.Infer

/-! CakeML inference-type rendering. Source and carrier review remains pending. -/
namespace Flapjack.Compiler.Inference.InferTDisplay
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.TypeSystemHOL
open Flapjack.Compiler.Inference.Infer

abbrev TypeNames (α : Type) := Namespace MlString MlString (α × SemanticT)

mutual
@[hol "cakeml/compiler/inference/infer_tScript.sml" "get_tyname_def"]
def getTyName {α : Type} (id : Nat) : TypeNames α → Option MlString
  | .bind entries modules => getTyNameEntries id entries modules
termination_by env => sizeOf env

/-- Flapjack recursion helper preserving the namespace's value-first order. -/
def getTyNameEntries {α : Type} (id : Nat) : List (MlString × (α × SemanticT)) →
    List (MlString × TypeNames α) → Option MlString
  | [], modules => getTyNameModules id modules
  | (name, (_, .app _ n)) :: rest, modules =>
    if n = id then some name else getTyNameEntries id rest modules
  | _ :: rest, modules => getTyNameEntries id rest modules
termination_by entries modules => sizeOf entries + sizeOf modules

/-- Flapjack recursion helper for qualified type names. -/
def getTyNameModules {α : Type} (id : Nat) : List (MlString × TypeNames α) → Option MlString
  | [] => none
  | (name, env) :: rest =>
    match getTyName id env with
    | some result => some (MlString.concat [name, ofString ".", result])
    | none => getTyNameModules id rest
termination_by modules => sizeOf modules
end

@[hol "cakeml/compiler/inference/infer_tScript.sml" "type_ident_to_string_def"]
def typeIdentToString {α : Type} (names : TypeNames α) (id : Nat) : MlString :=
  match id with
  | 0 => ofString "Array.array" | 1 => ofString "bool" | 2 => ofString "char"
  | 3 => ofString "exn" | 5 => ofString "int" | 6 => ofString "list"
  | 7 => ofString "ref" | 8 => ofString "string" | 10 => ofString "Vector.vector"
  | 11 => ofString "Word64.word" | 12 => ofString "Word8.word"
  | 13 => ofString "byte_array" | 14 => ofString "Double.double"
  | n => (getTyName n names).getD (ofString (toString n))

@[hol "cakeml/compiler/inference/infer_tScript.sml" "ty_var_name_def"]
def tyVarName (n : Nat) : MlString :=
  if n < 28 then .implode [39, BitVec.ofNat 8 (n + 97)]
  else MlString.concat [ofString "'", ofString (toString n)]

@[hol "cakeml/compiler/inference/infer_tScript.sml" "add_parens_def"]
def addParens (threshold : Nat) (part : MlString × Nat) : MlString :=
  if threshold < part.2 then MlString.concat [ofString "(", part.1, ofString ")"] else part.1

/-- Flapjack joining helper for HOL's `commas` list construction. -/
def joinParts (separator : MlString) (parts : List MlString) : MlString :=
  MlString.concat (parts.intersperse separator)

mutual
@[hol "cakeml/compiler/inference/infer_tScript.sml" "inf_type_to_string_rec_def"]
def inferTypeToStringRec {α : Type} (names : TypeNames α) : InferT → MlString × Nat
  | .uvar n => (MlString.concat [ofString "_", ofString (toString n)], 0)
  | .varDb n => (tyVarName n, 0)
  | .app ts id =>
    if id = 4 then
      match ts with
      | [a, b] => (MlString.concat [addParens 2 (inferTypeToStringRec names a), ofString " -> ",
          addParens 3 (inferTypeToStringRec names b)], 3)
      | _ => (ofString "<bad function type>", 0)
    else if id = 9 then
      match ts with
      | [] => (ofString "unit", 0)
      | [t] => inferTypeToStringRec names t
      | a :: b :: rest => (joinParts (ofString " * ")
          ((inferTypesToStringRec names (a :: b :: rest)).map (addParens 1)), 2)
    else
      match ts with
      | [] => (typeIdentToString names id, 0)
      | [t] => (MlString.concat [addParens 1 (inferTypeToStringRec names t), ofString " ",
          typeIdentToString names id], 1)
      | a :: b :: rest => (MlString.concat [ofString "(", joinParts (ofString ", ")
          ((inferTypesToStringRec names (a :: b :: rest)).map (addParens 5)), ofString ") ", typeIdentToString names id], 1)
termination_by t => sizeOf t

/-- The mutual list clause of the original inference-type rendering. -/
@[hol "cakeml/compiler/inference/infer_tScript.sml" "inf_type_to_string_rec_def"]
def inferTypesToStringRec {α : Type} (names : TypeNames α) : List InferT → List (MlString × Nat)
  | [] => []
  | t :: ts => inferTypeToStringRec names t :: inferTypesToStringRec names ts
termination_by ts => sizeOf ts
end

@[hol "cakeml/compiler/inference/infer_tScript.sml" "inf_type_to_string_def"]
def inferTypeToString {α : Type} (names : TypeNames α) (t : InferT) : MlString :=
  (inferTypeToStringRec names t).1

end Flapjack.Compiler.Inference.InferTDisplay
