import Flapjack.Basis.Pure.MlString

/-! Byte-oriented S-expression parser for the CakeML bootstrap input path.
The grammar follows HOL's `simpleSexpPEG`, but this direct, fuel-bounded
implementation has not been proved equivalent to the PEG. The executable's
S-expression path uses it before decoding the compiler AST. -/
namespace Flapjack.CakeParser.Sexp
open Flapjack.Basis.Pure.MlString

/-- S-expression carrier corresponding to the four HOL constructors. -/
inductive Sexp where
  | cons (head tail : Sexp)
  | sym (bytes : List HolChar)
  | num (value : Nat)
  | str (bytes : List HolChar)
  deriving Repr, DecidableEq

private def ascii (s : String) : List HolChar := (ofString s).explode
private def nil : Sexp := .sym (ascii "nil")
private def digit (c : HolChar) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57
private def printable (c : HolChar) : Bool := 32 ≤ c.toNat && c.toNat < 127
private def space (c : HolChar) : Bool := c.toNat == 32 || (9 ≤ c.toNat && c.toNat ≤ 13)
private def graph (c : HolChar) : Bool := printable c && !space c
private def firstSymbol (c : HolChar) : Bool :=
  graph c && c.toNat != 39 && c.toNat != 40 && c.toNat != 41 &&
    c.toNat != 46 && c.toNat != 34 && !digit c
private def symbol (c : HolChar) : Bool :=
  graph c && c.toNat != 39 && c.toNat != 40 && c.toNat != 41

private def skipSpace (input : List HolChar) : List HolChar := input.dropWhile space

/-- Parse a string's contents after its opening quote. Only backslash and
quote may be escaped; control characters are encoded at the AST layer. -/
private def parseString : List HolChar → Option (List HolChar × List HolChar)
  | [] => none
  | c :: rest =>
    if c.toNat == 34 then some ([], rest)
    else if c.toNat == 92 then
      match rest with
      | [] => none
      | escaped :: tail =>
        if escaped.toNat == 34 || escaped.toNat == 92 then do
          let (chars, tail) ← parseString tail
          some (escaped :: chars, tail)
        else none
    else if printable c then do
      let (chars, tail) ← parseString rest
      some (c :: chars, tail)
    else none

mutual
/-- Parse one expression, without consuming leading whitespace. -/
private def parseOne : Nat → List HolChar → Option (Sexp × List HolChar)
  | 0, _ => none
  | fuel + 1, input =>
    match input with
    | [] => none
    | c :: rest =>
      if digit c then
        let digits := input.takeWhile digit
        let value := digits.foldl (fun n d => 10 * n + (d.toNat - 48)) 0
        some (.num value, input.dropWhile digit)
      else if c.toNat == 40 then parseItems fuel rest []
      else if c.toNat == 34 then do
        let (chars, tail) ← parseString rest
        some (.str chars, tail)
      else if c.toNat == 39 then do
        let (quoted, tail) ← parseOne fuel (skipSpace rest)
        some (.cons (.sym (ascii "quote")) (.cons quoted nil), tail)
      else if firstSymbol c then
        let chars := c :: rest.takeWhile symbol
        some (.sym chars, rest.dropWhile symbol)
      else none

/-- Parse a list after its opening parenthesis, preserving improper tails. -/
private def parseItems : Nat → List HolChar → List Sexp → Option (Sexp × List HolChar)
  | 0, _, _ => none
  | fuel + 1, input, reversed =>
    let input := skipSpace input
    match input with
    | [] => none
    | c :: rest =>
      if c.toNat == 41 then
        some (reversed.foldl (fun tail head => .cons head tail) nil, rest)
      else if c.toNat == 46 && !reversed.isEmpty then do
        let (tail, afterTail) ← parseOne fuel (skipSpace rest)
        match skipSpace afterTail with
        | close :: afterClose =>
          if close.toNat == 41 then
            some (reversed.foldl (fun tail head => .cons head tail) tail, afterClose)
          else none
        | [] => none
      else do
        let (head, tail) ← parseOne fuel input
        parseItems fuel tail (head :: reversed)
end

/-- Parse exactly one S-expression and reject remaining non-whitespace input.
The bound is explicit and exhaustion is reported as failure. -/
def parseFuel (fuel : Nat) (input : List HolChar) : Option Sexp := do
  let (sexp, rest) ← parseOne fuel (skipSpace input)
  if (skipSpace rest).isEmpty then some sexp else none

/-- A source-size-derived bound for the direct parser. -/
def parse (input : List HolChar) : Option Sexp := parseFuel (2 * input.length + 2) input

end Flapjack.CakeParser.Sexp
