import Flapjack.SemanticPrimitivesHOL

/-! Source pattern matching, including the original distinction between a
non-matching value and a type error. Statement review is pending. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL Flapjack.NamespaceHOL

mutual
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "pmatch_def"]
def pmatch (envC : Namespace ModN ConN (Nat × Stamp)) (store : Store Value)
    (pattern : Pat) (value : Value) (env : List (VarN × Value)) : MatchResult (List (VarN × Value)) :=
  match pattern, value with
  | .pany, _ => .match env
  | .pvar name, _ => .match ((name, value) :: env)
  | .plit lit, .litv actual =>
    if lit = actual then .match env else if litSameType lit actual then .noMatch else .typeError
  | .pcon (some name) patterns, .conv (some actual) values =>
    match nsLookup envC name with
    | none => .typeError
    | some (arity, expected) =>
      if sameType expected actual && patterns.length == arity then
        if sameCtor expected actual then
          if values.length == arity then pmatchList envC store patterns values env else .typeError
        else .noMatch
      else .typeError
  | .pcon none patterns, .conv none values =>
    if patterns.length == values.length then pmatchList envC store patterns values env else .typeError
  | .pref pattern, .loc _ index =>
    match storeLookup index store with
    | some (.refv value) => pmatch envC store pattern value env
    | _ => .typeError
  | .pas pattern name, _ => pmatch envC store pattern value ((name, value) :: env)
  | .ptannot pattern _, _ => pmatch envC store pattern value env
  | _, _ => .typeError
termination_by sizeOf pattern

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "pmatch_def"]
def pmatchList (envC : Namespace ModN ConN (Nat × Stamp)) (store : Store Value)
    (patterns : List Pat) (values : List Value) (env : List (VarN × Value)) : MatchResult (List (VarN × Value)) :=
  match patterns, values with
  | [], [] => .match env
  | pattern :: patterns, value :: values =>
    match pmatch envC store pattern value env with
    | .noMatch => match pmatchList envC store patterns values env with
      | .typeError => .typeError
      | _ => .noMatch
    | .typeError => .typeError
    | .match env' => pmatchList envC store patterns values env'
  | _, _ => .typeError
termination_by sizeOf patterns
end

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "can_pmatch_all_def"]
def canPmatchAll (envC : Namespace ModN ConN (Nat × Stamp)) (store : Store Value)
    (patterns : List Pat) (value : Value) : Bool :=
  patterns.all fun pattern => match pmatch envC store pattern value [] with
    | .typeError => false
    | _ => true

end Flapjack.SemanticPrimitivesHOL
