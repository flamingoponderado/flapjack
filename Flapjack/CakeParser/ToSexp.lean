module

public import Flapjack.CakeParser.FromSexp.Ast
public import Flapjack.CakeParser.SexpPrint
public import Flapjack.CakeParser.FromSexp.Encode

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! CakeML AST encoding for the S-expression output path. The executable
aliases use the source-reviewed definitions in `FromSexp.Encode`; the whole
program wrapper is Flapjack-specific. -/
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

abbrev loc := FromSexp.locssexp
abbrev log := FromSexp.logsexp

abbrev exp := FromSexp.expsexp

abbrev dec := FromSexp.decsexp

def program (ds : List Dec) : Sexp := list (ds.map dec)
end Flapjack.CakeParser.ToSexp
