import Flapjack.CakeParser.Sexp
import Flapjack.AstHOL.Syntax

/-! CakeML's byte-oriented S-expression string encoding. -/
namespace Flapjack.CakeParser.FromSexp
open Flapjack.CakeParser.Sexp Flapjack.Basis.Pure.MlString
open Flapjack.NamespaceHOL
open Flapjack.AstHOL
open Flapjack.Misc.Location

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

mutual
/-- Encode CakeML type syntax. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "typesexp_def"]
def typesexp : AstT → Sexp
  | .atvar name => listsexp [.sym (ascii "Atvar"), sexstr name.explode]
  | .atfun left right => listsexp [.sym (ascii "Atfun"), typesexp left, typesexp right]
  | .attup types => listsexp [.sym (ascii "Attup"), listsexp (typesexpList types)]
  | .atapp types id => listsexp [.sym (ascii "Atapp"), listsexp (typesexpList types), idsexp id]
termination_by t => sizeOf t

/-- Recursive map used by `typesexp` for nested type lists. -/
def typesexpList : List AstT → List Sexp
  | [] => []
  | t :: ts => typesexp t :: typesexpList ts
termination_by ts => sizeOf ts
end

/-- Encode a source location point. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "locnsexp_def"]
def locnsexp : Locn → Sexp
  | .unknownPt => .sym (ascii "unk")
  | .eofPt => .sym (ascii "eof")
  | .posn row col => listsexp [.num row, .num col]

/-- Encode a source location. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "locssexp_def"]
def locssexp : Locs → Sexp
  | .locs a b => listsexp [locnsexp a, locnsexp b]

/-- Encode a short-circuit logical operator. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "logsexp_def"]
def logsexp : Lop → Sexp
  | .andalso => .sym (ascii "Andalso")
  | .orelse => .sym (ascii "Orelse")

/-- Encode CakeML literal syntax. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "litsexp_def"]
def litsexp : Lit → Sexp
  | .intLit (.ofNat n) => .num n
  | .intLit (.negSucc n) => listsexp [.sym (ascii "-"), .num (n + 1)]
  | .char c => listsexp [.sym (ascii "char"), sexstr [c]]
  | .strLit s => sexstr s.explode
  | .word8 w => listsexp [.sym (ascii "word8"), .num w.toNat]
  | .word64 w => listsexp [.sym (ascii "word64"), .num w.toNat]
  | .float64 w => listsexp [.sym (ascii "float64"), .num w.toNat]

mutual
/-- Encode CakeML pattern syntax. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "patsexp_def"]
def patsexp : Pat → Sexp
  | .pany => listsexp [.sym (ascii "Pany")]
  | .pvar name => sexstr name.explode
  | .plit lit => listsexp [.sym (ascii "Plit"), litsexp lit]
  | .pcon con pats => listsexp [.sym (ascii "Pcon"), optsexp (con.map idsexp), listsexp (patsexpList pats)]
  | .pref pat => listsexp [.sym (ascii "Pref"), patsexp pat]
  | .pas pat name => listsexp [.sym (ascii "Pas"), patsexp pat, sexstr name.explode]
  | .ptannot pat type => listsexp [.sym (ascii "Ptannot"), patsexp pat, typesexp type]
termination_by p => sizeOf p

/-- Recursive map used by `patsexp` for nested pattern lists. -/
def patsexpList : List Pat → List Sexp
  | [] => []
  | p :: ps => patsexp p :: patsexpList ps
termination_by ps => sizeOf ps
end

end Flapjack.CakeParser.FromSexp
