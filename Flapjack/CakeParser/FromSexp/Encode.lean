import Flapjack.CakeParser.Sexp
import Flapjack.AstHOL.Syntax

/-! CakeML's byte-oriented S-expression string encoding. -/
namespace Flapjack.CakeParser.FromSexp
open Flapjack.CakeParser.Sexp Flapjack.Basis.Pure.MlString
open Flapjack.NamespaceHOL

private def ascii (s : String) : List HolChar := (ofString s).explode

/-- Hexadecimal digit helper for control-byte encoding. -/
def hexDigit (n : Nat) : HolChar :=
  BitVec.ofNat 8 (if n < 10 then 48 + n else 65 + n - 10)

/-- Escape backslashes and non-printable bytes using the source encoding. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "encode_control_def"]
def encodeControl (bytes : List HolChar) : List HolChar := bytes.flatMap fun c =>
  let n := c.toNat
  if n == 92 then [c, c]
  else if 32 ≤ n && n < 127 then [c]
  else [BitVec.ofNat 8 92, hexDigit (n / 16), hexDigit (n % 16)]

/-- Construct an encoded string S-expression from a HOL byte string. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "SEXSTR_def"]
def sexstr (bytes : List HolChar) : Sexp := .str (encodeControl bytes)

/-- Encode a proper S-expression list. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "listsexp_def"]
def listsexp (xs : List Sexp) : Sexp := xs.foldr .cons (.sym (ascii "nil"))

/-- Encode an optional S-expression. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "optsexp_def"]
def optsexp : Option Sexp → Sexp
  | none => .sym (ascii "NONE")
  | some x => listsexp [.sym (ascii "SOME"), x]

/-- Encode a short or module-qualified CakeML identifier. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "idsexp_def"]
def idsexp : Ident MlString MlString → Sexp
  | .short name => listsexp [.sym (ascii "Short"), sexstr name.explode]
  | .long moduleName rest => listsexp [.sym (ascii "Long"), sexstr moduleName.explode, idsexp rest]

end Flapjack.CakeParser.FromSexp
