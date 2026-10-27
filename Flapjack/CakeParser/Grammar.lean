import Flapjack.CakeParser.Tokens

/-! Operator classes from CakeML's concrete grammar. -/
namespace Flapjack.CakeParser.Grammar
open Flapjack.Basis.Pure.MlString

/-- Multiplicative operator spelling. -/
@[hol "cakeml/semantics/gramScript.sml" "validMultSym_def"]
def validMultSym : List HolChar → Bool
  | c :: _ => c == 47 || c == 42 || c == 37 || c == 38
  | [] => false

/-- Additive operator spelling. -/
@[hol "cakeml/semantics/gramScript.sml" "validAddSym_def"]
def validAddSym : List HolChar → Bool
  | c :: rest => c == 43 || c == 45 || c == 94 || (c == 124 && !rest.isEmpty)
  | [] => false

/-- Relational operator spelling. -/
@[hol "cakeml/semantics/gramScript.sml" "validRelSym_def"]
def validRelSym : List HolChar → Bool
  | c :: rest => c == 60 || c == 62 || (!rest.isEmpty && (c == 61 || c == 126))
  | [] => false

/-- List operator spelling, excluding assignment. -/
@[hol "cakeml/semantics/gramScript.sml" "validListSym_def"]
def validListSym (s : List HolChar) : Bool :=
  match s with
  | c :: rest => c == 64 || (c == 58 && !rest.isEmpty && s != [58, 61])
  | [] => false

/-- Prefix operator spelling. -/
@[hol "cakeml/semantics/gramScript.sml" "validPrefixSym_def"]
def validPrefixSym (s : List HolChar) : Bool :=
  s == [126] || match s with | c :: _ => c == 33 || c == 63 | [] => false

end Flapjack.CakeParser.Grammar
