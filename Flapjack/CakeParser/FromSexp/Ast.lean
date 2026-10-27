import Flapjack.CakeParser.FromSexp.Operators

/-! Bounded CakeML AST decoding from S-expressions. Untagged pending complete
source and carrier correspondence review. -/
namespace Flapjack.CakeParser.FromSexp
open Flapjack.CakeParser.Sexp Flapjack.Basis.Pure.MlString Flapjack.AstHOL

private def ascii (s : String) : List HolChar := (ofString s).explode

/-- Decode an expression and all expression-bearing lists with explicit fuel. -/
def decodeExpFuel : Nat → Sexp → Option Exp
  | 0, _ => none
  | fuel + 1, sexp => do
    let (name, args) ← stripConstructor sexp
    let exp := decodeExpFuel fuel
    let clauses := decodeList (decodePair (decodePatternFuel fuel) exp)
    let funs := decodeList (decodePair destString (decodePair destString exp))
    match args with
    | [a] =>
      if name == ascii "Raise" then exp a |>.map Exp.raise
      else if name == ascii "Lit" then decodeLiteral a |>.map Exp.lit
      else if name == ascii "Var" then decodeIdFuel destString fuel a |>.map Exp.var
      else none
    | [a, b] =>
      if name == ascii "Handle" then do some (.handle (← exp a) (← clauses b))
      else if name == ascii "Con" then do
        some (.con (← decodeOption (decodeIdFuel destString fuel) a) (← decodeList exp b))
      else if name == ascii "Fun" then do some (.fn (← destString a) (← exp b))
      else if name == ascii "App" then do some (.app (← decodeOp a) (← decodeList exp b))
      else if name == ascii "Mat" then do some (.mat (← exp a) (← clauses b))
      else if name == ascii "Letrec" then do some (.letrec (← funs a) (← exp b))
      else if name == ascii "Tannot" then do some (.tannot (← exp a) (← decodeTypeFuel fuel b))
      else if name == ascii "Lannot" then do some (.lannot (← exp a) (← decodeLoc b))
      else none
    | [a, b, c] =>
      if name == ascii "Log" then do some (.log (← decodeLog a) (← exp b) (← exp c))
      else if name == ascii "If" then do some (.if_ (← exp a) (← exp b) (← exp c))
      else if name == ascii "Let" then do
        some (.let_ (← decodeOption destString a) (← exp b) (← exp c))
      else none
    | _ => none

/-- Decode a type definition's constructor and parameter lists. -/
def decodeTypeDefFuel (fuel : Nat) : Sexp → Option TypeDef :=
  decodeList (decodePair (decodeList destString)
    (decodePair destString (decodeList (decodePair destString (decodeList (decodeTypeFuel fuel))))))

/-- Decode declarations, including nested modules and local declarations. -/
def decodeDecFuel : Nat → Sexp → Option Dec
  | 0, _ => none
  | fuel + 1, sexp => do
    let (name, args) ← stripConstructor sexp
    let decs := decodeList (decodeDecFuel fuel)
    let funs := decodeList (decodePair destString (decodePair destString (decodeExpFuel fuel)))
    match args with
    | [a] => if name == ascii "Denv" then (destString a).map Dec.denv else none
    | [a, b] =>
      if name == ascii "Dletrec" then do some (.dletrec (← decodeLoc a) (← funs b))
      else if name == ascii "Dtype" then do some (.dtype (← decodeLoc a) (← decodeTypeDefFuel fuel b))
      else if name == ascii "Dmod" then do some (.dmod (← destString a) (← decs b))
      else if name == ascii "Dlocal" then do some (.dlocal (← decs a) (← decs b))
      else none
    | [a, b, c] =>
      if name == ascii "Dlet" then do
        some (.dlet (← decodeLoc a) (← decodePatternFuel fuel b) (← decodeExpFuel fuel c))
      else if name == ascii "Dexn" then do
        some (.dexn (← decodeLoc a) (← destString b) (← decodeList (decodeTypeFuel fuel) c))
      else none
    | [a, b, c, d] =>
      if name == ascii "Dtabbrev" then do
        some (.dtabbrev (← decodeLoc a) (← decodeList destString b) (← destString c) (← decodeTypeFuel fuel d))
      else none
    | _ => none

/-- Decode the proper top-level list of declarations. -/
def decodeProgramFuel (fuel : Nat) : Sexp → Option (List Dec) := decodeList (decodeDecFuel fuel)

end Flapjack.CakeParser.FromSexp
