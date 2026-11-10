module

public import Flapjack.CakeParser.Sexp
public import Flapjack.AstHOL.Syntax

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

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

/-- Encode an arithmetic operator. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "arithsexp_def"]
def arithsexp (op : Arith) : Sexp := .sym (ascii (match op with
  | .add => "Add" | .sub => "Sub" | .mul => "Mul" | .div => "Div"
  | .mod => "Mod" | .neg => "Neg" | .and => "And" | .xor => "Xor"
  | .or => "Or" | .not => "Not" | .abs => "Abs" | .sqrt => "Sqrt" | .fma => "FMA"))

/-- Encode a primitive type. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "prim_typesexp_def"]
def primTypesexp (type : PrimType) : Sexp := .sym (ascii (match type with
  | .boolT => "BoolT" | .intT => "IntT" | .charT => "CharT" | .strT => "StrT"
  | .wordT .w8 => "Word8T" | .wordT .w64 => "Word64T" | .float64T => "Float64T"))

/-- Encode a comparison test. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "testsexp_def"]
def testsexp (test : Test) : Sexp := .sym (ascii (match test with
  | .equal => "Equal"
  | .compare .lt => "Less" | .compare .leq => "LessEq"
  | .compare .gt => "Greater" | .compare .geq => "GreaterEq"
  | .altCompare .lt => "AltLess" | .altCompare .leq => "AltLessEq"
  | .altCompare .gt => "AltGreater" | .altCompare .geq => "AltGreaterEq"))

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

def opSym (s : String) : Sexp := .sym (ascii s)

def opShiftName : Shift → String
  | .lsl => "Lsl" | .lsr => "Lsr" | .asr => "Asr" | .ror => "Ror"
def opMode : ThunkMode → Sexp
  | .evaluated => opSym "Evaluated" | .notEvaluated => opSym "NotEvaluated"

/-- Encode an AST primitive operator. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "opsexp_def"]
def opsexp : Op → Sexp
  | .arith a p => .cons (opSym "Arith") (.cons (arithsexp a) (primTypesexp p))
  | .fromTo a b => .cons (opSym "FromTo") (.cons (primTypesexp a) (primTypesexp b))
  | .shift width sh n => .cons (opSym ("Shift" ++ (if width == .w8 then "8" else "64") ++ opShiftName sh)) (.num n)
  | .test t p => .cons (opSym "Test") (.cons (testsexp t) (primTypesexp p))
  | .thunkOp (.allocThunk m) => .cons (opSym "AllocThunk") (opMode m)
  | .thunkOp (.updateThunk m) => .cons (opSym "UpdateThunk") (opMode m)
  | .ffi s => .cons (opSym "FFI") (sexstr s.explode)
  | x => opSym <| match x with
    | .equality => "Equality" | .opapp => "Opapp" | .opassign => "Opassign"
    | .opref => "Opref" | .opderef => "Opderef" | .aw8alloc => "Aw8alloc"
    | .aw8sub => "Aw8sub" | .aw8length => "Aw8length" | .aw8update => "Aw8update"
    | .copyStrStr => "CopyStrStr" | .copyStrAw8 => "CopyStrAw8" | .copyAw8Str => "CopyAw8Str"
    | .copyAw8Aw8 => "CopyAw8Aw8" | .xorAw8StrUnsafe => "XorAw8Strunsafe"
    | .implode => "Implode" | .explode => "Explode" | .strsub => "Strsub"
    | .strlen => "Strlen" | .strcat => "Strcat" | .vfromList => "VfromList"
    | .vsub => "Vsub" | .vlength => "Vlength" | .aalloc => "Aalloc"
    | .aallocEmpty => "AallocEmpty" | .aallocFixed => "AallocFixed" | .asub => "Asub"
    | .alength => "Alength" | .aupdate => "Aupdate" | .vsubUnsafe => "Vsubunsafe"
    | .asubUnsafe => "Asubunsafe" | .aupdateUnsafe => "Aupdateunsafe"
    | .aw8subUnsafe => "Aw8subunsafe" | .aw8updateUnsafe => "Aw8updateunsafe"
    | .thunkOp .forceThunk => "ForceThunk" | .listAppend => "ListAppend"
    | .configGC => "ConfigGC" | .eval => "Eval" | .envId => "Envid"
    | _ => "" -- Covered by the outer cases.

def expsexpNode (name : String) (xs : List Sexp) : Sexp :=
  listsexp (.sym (ascii name) :: xs)

def expsexpString (s : MlString) : Sexp := sexstr s.explode

mutual
/-- Encode CakeML expression syntax. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "expsexp_def"]
def expsexp : Exp → Sexp
  | .raise e => expsexpNode "Raise" [expsexp e]
  | .handle e ps => expsexpNode "Handle" [expsexp e, listsexp (expsexpClauses ps)]
  | .lit l => expsexpNode "Lit" [litsexp l]
  | .con id es => expsexpNode "Con" [optsexp (id.map idsexp), listsexp (expsexpList es)]
  | .var id => expsexpNode "Var" [idsexp id]
  | .fn n e => expsexpNode "Fun" [expsexpString n, expsexp e]
  | .app o es => expsexpNode "App" [opsexp o, listsexp (expsexpList es)]
  | .log o a b => expsexpNode "Log" [logsexp o, expsexp a, expsexp b]
  | .if_ a b c => expsexpNode "If" [expsexp a, expsexp b, expsexp c]
  | .mat e ps => expsexpNode "Mat" [expsexp e, listsexp (expsexpClauses ps)]
  | .let_ n a b => expsexpNode "Let" [optsexp (n.map expsexpString), expsexp a, expsexp b]
  | .letrec fs e => expsexpNode "Letrec" [listsexp (expsexpFuns fs), expsexp e]
  | .tannot e t => expsexpNode "Tannot" [expsexp e, typesexp t]
  | .lannot e l => expsexpNode "Lannot" [expsexp e, locssexp l]
termination_by e => sizeOf e

def expsexpList : List Exp → List Sexp
  | [] => []
  | e :: es => expsexp e :: expsexpList es
termination_by es => sizeOf es

def expsexpClauses : List (Pat × Exp) → List Sexp
  | [] => []
  | (p, e) :: ps => .cons (patsexp p) (expsexp e) :: expsexpClauses ps
termination_by ps => sizeOf ps

def expsexpFuns : List (VarN × VarN × Exp) → List Sexp
  | [] => []
  | (f, x, e) :: fs => .cons (expsexpString f) (.cons (expsexpString x) (expsexp e)) :: expsexpFuns fs
termination_by fs => sizeOf fs
end

/-- Encode the constructor and parameter lists of a datatype definition. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "type_defsexp_def"]
def typeDefsexp (td : TypeDef) : Sexp := listsexp <| td.map fun (vs, name, cs) =>
  .cons (listsexp (vs.map expsexpString)) (.cons (expsexpString name) (listsexp (cs.map fun (c, ts) =>
    .cons (expsexpString c) (listsexp (ts.map typesexp)))))

mutual
/-- Encode CakeML declarations. -/
@[hol "cakeml/compiler/parsing/fromSexpScript.sml" "decsexp_def"]
def decsexp : Dec → Sexp
  | .dlet l p e => expsexpNode "Dlet" [locssexp l, patsexp p, expsexp e]
  | .dletrec l fs => expsexpNode "Dletrec" [locssexp l, listsexp (expsexpFuns fs)]
  | .dtype l td => expsexpNode "Dtype" [locssexp l, typeDefsexp td]
  | .dtabbrev l ns n t => expsexpNode "Dtabbrev" [locssexp l, listsexp (ns.map expsexpString), expsexpString n, typesexp t]
  | .dexn l n ts => expsexpNode "Dexn" [locssexp l, expsexpString n, listsexp (ts.map typesexp)]
  | .dmod n ds => expsexpNode "Dmod" [expsexpString n, listsexp (decsexpList ds)]
  | .dlocal a b => expsexpNode "Dlocal" [listsexp (decsexpList a), listsexp (decsexpList b)]
  | .denv n => expsexpNode "Denv" [expsexpString n]
termination_by d => sizeOf d

/-- Recursive map used by `decsexp` for nested declaration lists. -/
def decsexpList : List Dec → List Sexp
  | [] => []
  | d :: ds => decsexp d :: decsexpList ds
termination_by ds => sizeOf ds
end

end Flapjack.CakeParser.FromSexp
