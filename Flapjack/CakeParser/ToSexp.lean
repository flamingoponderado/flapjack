import Flapjack.CakeParser.FromSexp.Ast
import Flapjack.CakeParser.SexpPrint
import Flapjack.CakeParser.FromSexp.Encode

/-! CakeML AST encoding for the S-expression output path. The recursive
traversals are executable infrastructure pending source correspondence review;
they are not yet tagged as HOL ports. -/
namespace Flapjack.CakeParser.ToSexp
open Flapjack.CakeParser.Sexp Flapjack.Basis.Pure.MlString
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Misc.Location

private def ascii (s : String) : List HolChar := (ofString s).explode
def sym (s : String) : Sexp := .sym (ascii s)
abbrev list := FromSexp.listsexp
def node (s : String) (xs : List Sexp) : Sexp := list (sym s :: xs)
abbrev option := FromSexp.optsexp

abbrev hexDigit := FromSexp.hexDigit
abbrev encodeControl := FromSexp.encodeControl

def str (s : MlString) : Sexp := FromSexp.sexstr s.explode

abbrev ident := FromSexp.idsexp

abbrev type := FromSexp.typesexp

abbrev literal := FromSexp.litsexp

abbrev pattern := FromSexp.patsexp

abbrev op := FromSexp.opsexp

abbrev locPoint := FromSexp.locnsexp
abbrev loc := FromSexp.locssexp
abbrev log := FromSexp.logsexp

abbrev exp := FromSexp.expsexp

def typeDef (td : TypeDef) : Sexp := list <| td.map fun (vs, name, cs) =>
  .cons (list (vs.map str)) (.cons (str name) (list (cs.map fun (c, ts) =>
    .cons (str c) (list (ts.map type)))))

mutual
def dec : Dec → Sexp
  | .dlet l p e => node "Dlet" [loc l, pattern p, exp e]
  | .dletrec l fs => node "Dletrec" [loc l, list (fs.map fun (f, x, e) => .cons (str f) (.cons (str x) (exp e)))]
  | .dtype l td => node "Dtype" [loc l, typeDef td]
  | .dtabbrev l ns n t => node "Dtabbrev" [loc l, list (ns.map str), str n, type t]
  | .dexn l n ts => node "Dexn" [loc l, str n, list (ts.map type)]
  | .dmod n ds => node "Dmod" [str n, list (decList ds)]
  | .dlocal a b => node "Dlocal" [list (decList a), list (decList b)]
  | .denv n => node "Denv" [str n]
termination_by d => sizeOf d

private def decList : List Dec → List Sexp
  | [] => []
  | d :: ds => dec d :: decList ds
termination_by ds => sizeOf ds
end

def program (ds : List Dec) : Sexp := list (ds.map dec)
end Flapjack.CakeParser.ToSexp
