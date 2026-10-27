import Flapjack.CakeParser.Sexp
import Flapjack.AstHOL.Syntax

/-! Shared conversions for CakeML's S-expression AST format, following
`compiler/parsing/fromSexpScript.sml`. The S-expression carrier and bounded
identifier traversal have not yet completed HOL correspondence review; these
declarations are untagged. The executable's S-expression path uses them. -/
namespace Flapjack.CakeParser.FromSexp
open Flapjack.CakeParser.Sexp Flapjack.Basis.Pure.MlString
open Flapjack.AstHOL Flapjack.NamespaceHOL

private def ascii (s : String) : List HolChar := (ofString s).explode
private def isPrint (c : HolChar) : Bool := 32 ≤ c.toNat && c.toNat < 127

private def upperHex (c : HolChar) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 65 ≤ n && n ≤ 70 then some (n - 65 + 10)
  else none

/-- Decode the canonical control-character encoding used inside AST strings.
Printable characters must remain literal; only uppercase hexadecimal escapes
of non-printable bytes and doubled backslashes are accepted. -/
def decodeControl : List HolChar → Option (List HolChar)
  | [] => some []
  | c :: rest =>
    if c.toNat == 92 then
      match rest with
      | d :: tail =>
        if d.toNat == 92 then
          (decodeControl tail).map (c :: ·)
        else match tail with
          | e :: tail => do
            let hi ← upperHex d
            let lo ← upperHex e
            let byte := BitVec.ofNat 8 (16 * hi + lo)
            if isPrint byte then none else
              (decodeControl tail).map (byte :: ·)
          | [] => none
      | [] => none
    else if isPrint c then (decodeControl rest).map (c :: ·) else none

/-- Decode a string-valued S-expression to the HOL byte-string carrier. -/
def destString : Sexp → Option MlString
  | .str data => (decodeControl data).map MlString.implode
  | _ => none

/-- Decode a proper S-expression list, rejecting an improper tail. -/
def decodeList (decode : Sexp → Option α) : Sexp → Option (List α)
  | .cons head tail => do
    let head ← decode head
    let tail ← decodeList decode tail
    some (head :: tail)
  | .sym name => if name == ascii "nil" then some [] else none
  | _ => none

/-- Decode a pair from a cons cell; the tail is the second component itself. -/
def decodePair {α β : Type} (left : Sexp → Option α) (right : Sexp → Option β) : Sexp → Option (α × β)
  | .cons a b => do some (← left a, ← right b)
  | _ => none

/-- Unpack a constructor name and its proper argument list. -/
def stripConstructor : Sexp → Option (List HolChar × List Sexp)
  | .cons (.sym name) args => do some (name, ← decodeList some args)
  | _ => none

/-- Decode HOL's `NONE` or `(SOME x)` representation. -/
def decodeOption (decode : Sexp → Option α) (sexp : Sexp) : Option (Option α) :=
  match sexp with
  | .sym name => if name == ascii "NONE" then some none else none
  | _ => do
    let (name, args) ← stripConstructor sexp
    match args with
    | [value] => if name == ascii "SOME" then (decode value).map some else none
    | _ => none

/-- Decode short and module-qualified identifiers, with an explicit traversal
bound. Exhaustion returns `none`. -/
def decodeIdFuel (decode : Sexp → Option α) : Nat → Sexp → Option (Ident MlString α)
  | 0, _ => none
  | fuel + 1, sexp => do
    let (name, args) ← stripConstructor sexp
    match args with
    | [value] =>
      if name == ascii "Short" then (decode value).map Ident.short else none
    | [modName, rest] =>
      if name == ascii "Long" then do
        some (.long (← destString modName) (← decodeIdFuel decode fuel rest))
      else none
    | _ => none

/-- Decode all six literal forms, including the original word bounds and
rejection of negative zero. -/
def decodeLiteral (sexp : Sexp) : Option Lit :=
  match sexp with
  | .num n => some (.intLit (Int.ofNat n))
  | .str _ => (destString sexp).map Lit.strLit
  | _ => do
    let (name, args) ← stripConstructor sexp
    match args with
    | [arg] =>
      if name == ascii "-" then
        match arg with
        | .num n => if n == 0 then none else some (.intLit (-(Int.ofNat n)))
        | _ => none
      else if name == ascii "char" then do
        let s ← destString arg
        match s.explode with
        | [c] => some (.char c)
        | _ => none
      else match arg with
        | .num n =>
          if name == ascii "word8" && n < 256 then some (.word8 (BitVec.ofNat 8 n))
          else if name == ascii "word64" && n < 2 ^ 64 then some (.word64 (BitVec.ofNat 64 n))
          else if name == ascii "float64" && n < 2 ^ 64 then some (.float64 (BitVec.ofNat 64 n))
          else none
        | _ => none
    | _ => none

/-- Decode a source location point. -/
def decodeLocPoint (sexp : Sexp) : Option Misc.Location.Locn :=
  match sexp with
  | .sym name =>
    if name == ascii "unk" then some .unknownPt
    else if name == ascii "eof" then some .eofPt else none
  | _ => do
    let args ← decodeList some sexp
    match args with
    | [.num row, .num col] => some (.posn row col)
    | _ => none

/-- Decode a pair of source location points. -/
def decodeLoc (sexp : Sexp) : Option Misc.Location.Locs := do
  let args ← decodeList some sexp
  match args with
  | [start, stop] => some (.locs (← decodeLocPoint start) (← decodeLocPoint stop))
  | _ => none

/-- Decode CakeML type syntax, with an explicit recursion bound. -/
def decodeTypeFuel : Nat → Sexp → Option AstT
  | 0, _ => none
  | fuel + 1, sexp => do
    let (name, args) ← stripConstructor sexp
    match args with
    | [a] =>
      if name == ascii "Atvar" then (destString a).map AstT.atvar
      else if name == ascii "Attup" then (decodeList (decodeTypeFuel fuel) a).map AstT.attup
      else none
    | [a, b] =>
      if name == ascii "Atfun" then do
        some (.atfun (← decodeTypeFuel fuel a) (← decodeTypeFuel fuel b))
      else if name == ascii "Atapp" then do
        some (.atapp (← decodeList (decodeTypeFuel fuel) a) (← decodeIdFuel destString fuel b))
      else none
    | _ => none

/-- Decode CakeML patterns, with an explicit recursion bound. -/
def decodePatternFuel : Nat → Sexp → Option Pat
  | 0, _ => none
  | fuel + 1, sexp =>
    match sexp with
    | .str _ => (destString sexp).map Pat.pvar
    | _ => do
      let (name, args) ← stripConstructor sexp
      match args with
      | [] => if name == ascii "Pany" then some .pany else none
      | [a] =>
        if name == ascii "Plit" then (decodeLiteral a).map Pat.plit
        else if name == ascii "Pref" then (decodePatternFuel fuel a).map Pat.pref
        else none
      | [a, b] =>
        if name == ascii "Pcon" then do
          some (.pcon (← decodeOption (decodeIdFuel destString fuel) a)
            (← decodeList (decodePatternFuel fuel) b))
        else if name == ascii "Pas" then do
          some (.pas (← decodePatternFuel fuel a) (← destString b))
        else if name == ascii "Ptannot" then do
          some (.ptannot (← decodePatternFuel fuel a) (← decodeTypeFuel fuel b))
        else none
      | _ => none

end Flapjack.CakeParser.FromSexp
