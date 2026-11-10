module

public import Flapjack.CakeParser.FromSexp.Operators

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! CakeML AST decoding from S-expressions. Expression and declaration
decoding use source-reviewed structural recursion. -/
namespace Flapjack.CakeParser.FromSexp
open Flapjack.CakeParser.Sexp Flapjack.Basis.Pure.MlString Flapjack.AstHOL

private def ascii (s : String) : List HolChar := (ofString s).explode

/-- Decode an expression and all expression-bearing lists with explicit fuel. -/
def decodeExpFuel : Nat → Sexp → Option Exp
  | 0, _ => none
  | fuel + 1, sexp => do
    let (name, args) ← stripConstructor sexp
    let exp := decodeExpFuel fuel
    let clauses := decodeList (decodePair decodePattern exp)
    let funs := decodeList (decodePair destString (decodePair destString exp))
    match args with
    | [a] =>
      if name == ascii "Raise" then exp a |>.map Exp.raise
      else if name == ascii "Lit" then decodeLiteral a |>.map Exp.lit
      else if name == ascii "Var" then decodeId destString a |>.map Exp.var
      else none
    | [a, b] =>
      if name == ascii "Handle" then do some (.handle (← exp a) (← clauses b))
      else if name == ascii "Con" then do
        some (.con (← decodeOption (decodeId destString) a) (← decodeList exp b))
      else if name == ascii "Fun" then do some (.fn (← destString a) (← exp b))
      else if name == ascii "App" then do some (.app (← decodeOp a) (← decodeList exp b))
      else if name == ascii "Mat" then do some (.mat (← exp a) (← clauses b))
      else if name == ascii "Letrec" then do some (.letrec (← funs a) (← exp b))
      else if name == ascii "Tannot" then do some (.tannot (← exp a) (← decodeType b))
      else if name == ascii "Lannot" then do some (.lannot (← exp a) (← decodeLoc b))
      else none
    | [a, b, c] =>
      if name == ascii "Log" then do some (.log (← decodeLog a) (← exp b) (← exp c))
      else if name == ascii "If" then do some (.if_ (← exp a) (← exp b) (← exp c))
      else if name == ascii "Let" then do
        some (.let_ (← decodeOption destString a) (← exp b) (← exp c))
      else none
    | _ => none

mutual
/-- Decode expressions by recursion on the input S-expression. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexpexp_def"]
def decodeExp : Sexp → Option Exp
  | .cons (.sym name) (.cons a (.sym terminator)) =>
    if terminator != ascii "nil" then none
    else if name == ascii "Raise" then (decodeExp a).map Exp.raise
    else if name == ascii "Lit" then (decodeLiteral a).map Exp.lit
    else if name == ascii "Var" then (decodeId destString a).map Exp.var
    else none
  | .cons (.sym name) (.cons a (.cons b (.sym terminator))) =>
    if terminator != ascii "nil" then none
    else if name == ascii "Handle" then do some (.handle (← decodeExp a) (← decodeClauses b))
    else if name == ascii "Con" then do
      some (.con (← decodeOption (decodeId destString) a) (← decodeExpList b))
    else if name == ascii "Fun" then do some (.fn (← destString a) (← decodeExp b))
    else if name == ascii "App" then do some (.app (← decodeOp a) (← decodeExpList b))
    else if name == ascii "Mat" then do some (.mat (← decodeExp a) (← decodeClauses b))
    else if name == ascii "Letrec" then do some (.letrec (← decodeFunctions a) (← decodeExp b))
    else if name == ascii "Tannot" then do some (.tannot (← decodeExp a) (← decodeType b))
    else if name == ascii "Lannot" then do some (.lannot (← decodeExp a) (← decodeLoc b))
    else none
  | .cons (.sym name) (.cons a (.cons b (.cons c (.sym terminator)))) =>
    if terminator != ascii "nil" then none
    else if name == ascii "Log" then do some (.log (← decodeLog a) (← decodeExp b) (← decodeExp c))
    else if name == ascii "If" then do some (.if_ (← decodeExp a) (← decodeExp b) (← decodeExp c))
    else if name == ascii "Let" then do
      some (.let_ (← decodeOption destString a) (← decodeExp b) (← decodeExp c))
    else none
  | _ => none
termination_by sexp => sizeOf sexp

/-- Flapjack recursion helper for proper lists of expressions. -/
def decodeExpList : Sexp → Option (List Exp)
  | .cons head tail => do some ((← decodeExp head) :: (← decodeExpList tail))
  | .sym name => if name == ascii "nil" then some [] else none
  | _ => none
termination_by sexp => sizeOf sexp

/-- Flapjack recursion helper for pattern/expression pairs. -/
def decodeClauses : Sexp → Option (List (Pat × Exp))
  | .cons (.cons pat body) tail => do
    some ((← decodePattern pat, ← decodeExp body) :: (← decodeClauses tail))
  | .sym name => if name == ascii "nil" then some [] else none
  | _ => none
termination_by sexp => sizeOf sexp

/-- Flapjack recursion helper for function-name, argument and body triples. -/
def decodeFunctions : Sexp → Option (List (MlString × MlString × Exp))
  | .cons (.cons name (.cons arg body)) tail => do
    some ((← destString name, ← destString arg, ← decodeExp body) :: (← decodeFunctions tail))
  | .sym name => if name == ascii "nil" then some [] else none
  | _ => none
termination_by sexp => sizeOf sexp
end

/-- Decode a type definition's constructor and parameter lists. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexptype_def_def"]
def decodeTypeDef : Sexp → Option TypeDef :=
  decodeList (decodePair (decodeList destString)
    (decodePair destString (decodeList (decodePair destString decodeTypeList))))

mutual
/-- Decode declarations by recursion on the input S-expression. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "sexpdec_def"]
def decodeDec : Sexp → Option Dec
  | .cons (.sym name) (.cons a (.sym terminator)) =>
    if name == ascii "Denv" && terminator == ascii "nil" then (destString a).map Dec.denv else none
  | .cons (.sym name) (.cons a (.cons b (.sym terminator))) =>
    if terminator != ascii "nil" then none
    else if name == ascii "Dletrec" then do some (.dletrec (← decodeLoc a) (← decodeFunctions b))
    else if name == ascii "Dtype" then do some (.dtype (← decodeLoc a) (← decodeTypeDef b))
    else if name == ascii "Dmod" then do some (.dmod (← destString a) (← decodeDecList b))
    else if name == ascii "Dlocal" then do some (.dlocal (← decodeDecList a) (← decodeDecList b))
    else none
  | .cons (.sym name) (.cons a (.cons b (.cons c (.sym terminator)))) =>
    if terminator != ascii "nil" then none
    else if name == ascii "Dlet" then do
      some (.dlet (← decodeLoc a) (← decodePattern b) (← decodeExp c))
    else if name == ascii "Dexn" then do
      some (.dexn (← decodeLoc a) (← destString b) (← decodeTypeList c))
    else none
  | .cons (.sym name) (.cons a (.cons b (.cons c (.cons d (.sym terminator))))) =>
    if terminator != ascii "nil" then none
    else if name == ascii "Dtabbrev" then do
      some (.dtabbrev (← decodeLoc a) (← decodeList destString b) (← destString c) (← decodeType d))
    else none
  | _ => none
termination_by sexp => sizeOf sexp

/-- Flapjack recursion helper for a proper list of declarations. -/
def decodeDecList : Sexp → Option (List Dec)
  | .cons head tail => do some ((← decodeDec head) :: (← decodeDecList tail))
  | .sym name => if name == ascii "nil" then some [] else none
  | _ => none
termination_by sexp => sizeOf sexp
end

end Flapjack.CakeParser.FromSexp
