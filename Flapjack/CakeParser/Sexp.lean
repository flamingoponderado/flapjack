module

public import Flapjack.Basis.Pure.MlString
public import Flapjack.HolRef

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Byte-oriented S-expression parser for the CakeML bootstrap input path.
The grammar follows HOL's `simpleSexpPEG`, but this direct implementation has
not been proved equivalent to the PEG. The executable's
S-expression path uses it before decoding the compiler AST. -/
namespace Flapjack.CakeParser.Sexp
open Flapjack.Basis.Pure.MlString

/-- S-expression carrier corresponding to the four HOL constructors. -/
@[hol "HOL/examples/formal-languages/context-free/simpleSexpScript.sml" "sexp"]
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

/-- Dropping a prefix cannot increase the remaining input. -/
private theorem dropWhile_length (p : HolChar → Bool) (xs : List HolChar) :
    (xs.dropWhile p).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.dropWhile_cons]
    split
    · simp only [List.length_cons]
      omega
    · simp

private theorem skipSpace_length (xs : List HolChar) : (skipSpace xs).length ≤ xs.length :=
  dropWhile_length space xs

/-- A successful string scan returns a suffix of its input. -/
private theorem parseString_remaining (xs chars rest : List HolChar)
    (h : parseString xs = some (chars, rest)) : rest.length ≤ xs.length := by
  cases xs with
  | nil => simp [parseString] at h
  | cons x xs =>
    rw [parseString.eq_def] at h
    dsimp only at h
    by_cases quote : x.toNat = 34
    · have : rest = xs := by simpa [quote] using (congrArg (Option.map Prod.snd) h).symm
      subst rest
      simp
    · by_cases slash : x.toNat = 92
      · cases xs with
        | nil => simp [slash] at h
        | cons escaped tail =>
          by_cases valid : escaped.toNat = 34 ∨ escaped.toNat = 92
          · cases hs : parseString tail with
            | none => simp [slash, valid, hs] at h
            | some pair =>
              obtain ⟨cs, rem⟩ := pair
              have equal : rem = rest := by
                simpa [quote, slash, valid, hs] using congrArg (Option.map Prod.snd) h
              subst rest
              have bound := parseString_remaining tail cs rem hs
              simp only [List.length_cons]
              omega
          · simp [slash, valid] at h
      · by_cases valid : printable x = true
        · cases hs : parseString xs with
          | none => simp [quote, slash, valid, hs] at h
          | some pair =>
            obtain ⟨cs, rem⟩ := pair
            have equal : rem = rest := by
              simpa [quote, slash, valid, hs] using congrArg (Option.map Prod.snd) h
            subst rest
            have bound := parseString_remaining xs cs rem hs
            simp only [List.length_cons]
            omega
        · simp [quote, slash, valid] at h
termination_by xs.length

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

/-- A successful parse returns a strictly shorter remaining input. -/
private abbrev Consumed (input : List HolChar) :=
  { result : Sexp × List HolChar // result.2.length < input.length }

mutual
/-- Parse one expression, with consumption checked in the result type. -/
private def parseOneTotal (input : List HolChar) : Option (Consumed input) := by
  cases input with
  | nil => exact none
  | cons c rest =>
    by_cases hd : digit c = true
    · let digits := (c :: rest).takeWhile digit
      let value := digits.foldl (fun n d => 10 * n + (d.toNat - 48)) 0
      refine some ⟨(.num value, (c :: rest).dropWhile digit), ?_⟩
      simp only [List.dropWhile_cons, hd, ↓reduceIte, List.length_cons]
      have bound := dropWhile_length digit rest
      omega
    · by_cases openList : c.toNat = 40
      · cases h : parseItemsTotal rest [] with
        | none => exact none
        | some result =>
          exact some ⟨result.1, by simp only [List.length_cons]; omega⟩
      · by_cases quote : c.toNat = 34
        · cases h : parseString rest with
          | none => exact none
          | some result =>
            obtain ⟨chars, tail⟩ := result
            have bound := parseString_remaining rest chars tail h
            exact some ⟨(.str chars, tail), by simp only [List.length_cons]; omega⟩
        · by_cases apostrophe : c.toNat = 39
          · cases h : parseOneTotal (skipSpace rest) with
            | none => exact none
            | some result =>
              have bound := skipSpace_length rest
              exact some ⟨(.cons (.sym (ascii "quote")) (.cons result.1.1 nil), result.1.2), by
                simp only [List.length_cons]; omega⟩
          · by_cases sym : firstSymbol c = true
            · let chars := c :: rest.takeWhile symbol
              have bound := dropWhile_length symbol rest
              exact some ⟨(.sym chars, rest.dropWhile symbol), by simp only [List.length_cons]; omega⟩
            · exact none
termination_by (input.length, 0)
decreasing_by
  all_goals simp_wf
  all_goals have bound := skipSpace_length rest; omega

/-- Parse the contents of a list while preserving improper tails. -/
private def parseItemsTotal (input : List HolChar) (reversed : List Sexp) : Option (Consumed input) := by
  let trimmed := skipSpace input
  have trimBound : trimmed.length ≤ input.length := skipSpace_length input
  cases htrim : trimmed with
  | nil => exact none
  | cons c rest =>
    by_cases close : c.toNat = 41
    · exact some ⟨(reversed.foldl (fun tail head => .cons head tail) nil, rest), by
        change rest.length < input.length
        simp only [htrim, List.length_cons] at trimBound
        omega⟩
    · by_cases dot : c.toNat = 46 ∧ reversed.isEmpty = false
      · cases h : parseOneTotal (skipSpace rest) with
        | none => exact none
        | some tailResult =>
          let after := skipSpace tailResult.1.2
          have afterBound : after.length ≤ tailResult.1.2.length := skipSpace_length _
          have restBound : (skipSpace rest).length ≤ rest.length := skipSpace_length rest
          cases hafter : after with
          | nil => exact none
          | cons endChar afterClose =>
            if endChar.toNat == 41 then
              exact some ⟨(reversed.foldl (fun tail head => .cons head tail) tailResult.1.1, afterClose), by
                change afterClose.length < input.length
                simp only [htrim, List.length_cons] at trimBound
                simp only [hafter, List.length_cons] at afterBound
                omega⟩
            else exact none
      · cases h : parseOneTotal trimmed with
        | none => exact none
        | some headResult =>
          cases ht : parseItemsTotal headResult.1.2 (headResult.1.1 :: reversed) with
          | none => exact none
          | some result =>
            exact some ⟨result.1, by omega⟩
termination_by (input.length, 1)
decreasing_by
  all_goals simp_wf
  · apply Prod.Lex.left
    have bound := skipSpace_length rest
    simp only [htrim, List.length_cons] at trimBound
    omega
  · by_cases equal : (skipSpace input).length = input.length
    · rw [equal]
      apply Prod.Lex.right
      decide
    · apply Prod.Lex.left
      dsimp [trimmed] at trimBound
      omega
  · apply Prod.Lex.left
    omega
end

/-- Parse exactly one S-expression and reject remaining non-whitespace input.
The bound is explicit and exhaustion is reported as failure. -/
def parseFuel (fuel : Nat) (input : List HolChar) : Option Sexp := do
  let (sexp, rest) ← parseOne fuel (skipSpace input)
  if (skipSpace rest).isEmpty then some sexp else none

/-- Parse exactly one S-expression using the total, consumption-checked parser.
This Flapjack parser has not yet been proved equivalent to the HOL PEG. -/
def parse (input : List HolChar) : Option Sexp := do
  let result ← parseOneTotal (skipSpace input)
  if (skipSpace result.1.2).isEmpty then some result.1.1 else none

end Flapjack.CakeParser.Sexp
