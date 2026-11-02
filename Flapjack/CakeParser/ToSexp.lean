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

abbrev typeDef := FromSexp.typeDefsexp
abbrev dec := FromSexp.decsexp

def program (ds : List Dec) : Sexp := list (ds.map dec)
end Flapjack.CakeParser.ToSexp
