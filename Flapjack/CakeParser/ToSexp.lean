import Flapjack.CakeParser.FromSexp.Ast
import Flapjack.CakeParser.SexpPrint

/-! CakeML AST encoding for the S-expression output path. The recursive
traversals are executable infrastructure pending termination and source
correspondence proofs; they are not yet tagged as HOL ports. -/
namespace Flapjack.CakeParser.ToSexp
open Flapjack.CakeParser.Sexp Flapjack.Basis.Pure.MlString
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Misc.Location

private def ascii (s : String) : List HolChar := (ofString s).explode
private instance : Inhabited Sexp := ⟨.sym []⟩
def sym (s : String) : Sexp := .sym (ascii s)
def list (xs : List Sexp) : Sexp := xs.foldr .cons (sym "nil")
def node (s : String) (xs : List Sexp) : Sexp := list (sym s :: xs)
def option (s : Option Sexp) : Sexp := match s with
  | none => sym "NONE"
  | some x => node "SOME" [x]

private def hexDigit (n : Nat) : HolChar :=
  BitVec.ofNat 8 (if n < 10 then 48 + n else 65 + n - 10)

def encodeControl (bytes : List HolChar) : List HolChar := bytes.flatMap fun c =>
  let n := c.toNat
  if n == 92 then [c, c]
  else if 32 ≤ n && n < 127 then [c]
  else [BitVec.ofNat 8 92, hexDigit (n / 16), hexDigit (n % 16)]

def str (s : MlString) : Sexp := .str (encodeControl s.explode)

def ident : Ident MlString MlString → Sexp
  | .short n => node "Short" [str n]
  | .long m n => node "Long" [str m, ident n]

partial def type : AstT → Sexp
  | .atvar n => node "Atvar" [str n]
  | .atfun a b => node "Atfun" [type a, type b]
  | .attup ts => node "Attup" [list (ts.map type)]
  | .atapp ts id => node "Atapp" [list (ts.map type), ident id]

def literal : Lit → Sexp
  | .intLit (.ofNat n) => .num n
  | .intLit (.negSucc n) => node "-" [.num (n + 1)]
  | .char c => node "char" [.str (encodeControl [c])]
  | .strLit s => str s
  | .word8 w => node "word8" [.num w.toNat]
  | .word64 w => node "word64" [.num w.toNat]
  | .float64 w => node "float64" [.num w.toNat]

partial def pattern : Pat → Sexp
  | .pany => node "Pany" []
  | .pvar n => str n
  | .plit l => node "Plit" [literal l]
  | .pcon cn ps => node "Pcon" [option (cn.map ident), list (ps.map pattern)]
  | .pref p => node "Pref" [pattern p]
  | .pas p n => node "Pas" [pattern p, str n]
  | .ptannot p t => node "Ptannot" [pattern p, type t]

private def arith : Arith → Sexp := fun x => sym <| match x with
  | .add => "Add" | .sub => "Sub" | .mul => "Mul" | .div => "Div"
  | .mod => "Mod" | .neg => "Neg" | .and => "And" | .xor => "Xor"
  | .or => "Or" | .not => "Not" | .abs => "Abs" | .sqrt => "Sqrt" | .fma => "FMA"
private def primType : PrimType → Sexp := fun x => sym <| match x with
  | .boolT => "BoolT" | .intT => "IntT" | .charT => "CharT" | .strT => "StrT"
  | .wordT .w8 => "Word8T" | .wordT .w64 => "Word64T" | .float64T => "Float64T"
private def cmpName : Opb → String
  | .lt => "Less" | .leq => "LessEq" | .gt => "Greater" | .geq => "GreaterEq"
private def test : Test → Sexp
  | .equal => sym "Equal"
  | .compare c => sym (cmpName c)
  | .altCompare c => sym ("Alt" ++ cmpName c)
private def shiftName : Shift → String
  | .lsl => "Lsl" | .lsr => "Lsr" | .asr => "Asr" | .ror => "Ror"
private def mode : ThunkMode → Sexp
  | .evaluated => sym "Evaluated" | .notEvaluated => sym "NotEvaluated"

def op : Op → Sexp
  | .arith a p => .cons (sym "Arith") (.cons (arith a) (primType p))
  | .fromTo a b => .cons (sym "FromTo") (.cons (primType a) (primType b))
  | .shift width sh n => .cons (sym ("Shift" ++ (if width == .w8 then "8" else "64") ++ shiftName sh)) (.num n)
  | .test t p => .cons (sym "Test") (.cons (test t) (primType p))
  | .thunkOp (.allocThunk m) => .cons (sym "AllocThunk") (mode m)
  | .thunkOp (.updateThunk m) => .cons (sym "UpdateThunk") (mode m)
  | .ffi s => .cons (sym "FFI") (str s)
  | x => sym <| match x with
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

def locPoint : Locn → Sexp
  | .unknownPt => sym "unk" | .eofPt => sym "eof"
  | .posn row col => list [.num row, .num col]
def loc : Locs → Sexp
  | .locs a b => list [locPoint a, locPoint b]

def log : Lop → Sexp
  | .andalso => sym "Andalso" | .orelse => sym "Orelse"

partial def exp : Exp → Sexp
  | .raise e => node "Raise" [exp e]
  | .handle e ps => node "Handle" [exp e, list (ps.map fun (p, e) => .cons (pattern p) (exp e))]
  | .lit l => node "Lit" [literal l]
  | .con id es => node "Con" [option (id.map ident), list (es.map exp)]
  | .var id => node "Var" [ident id]
  | .fn n e => node "Fun" [str n, exp e]
  | .app o es => node "App" [op o, list (es.map exp)]
  | .log o a b => node "Log" [log o, exp a, exp b]
  | .if_ a b c => node "If" [exp a, exp b, exp c]
  | .mat e ps => node "Mat" [exp e, list (ps.map fun (p, e) => .cons (pattern p) (exp e))]
  | .let_ n a b => node "Let" [option (n.map str), exp a, exp b]
  | .letrec fs e => node "Letrec" [list (fs.map fun (f, x, e) => .cons (str f) (.cons (str x) (exp e))), exp e]
  | .tannot e t => node "Tannot" [exp e, type t]
  | .lannot e l => node "Lannot" [exp e, loc l]

def typeDef (td : TypeDef) : Sexp := list <| td.map fun (vs, name, cs) =>
  .cons (list (vs.map str)) (.cons (str name) (list (cs.map fun (c, ts) =>
    .cons (str c) (list (ts.map type)))))

partial def dec : Dec → Sexp
  | .dlet l p e => node "Dlet" [loc l, pattern p, exp e]
  | .dletrec l fs => node "Dletrec" [loc l, list (fs.map fun (f, x, e) => .cons (str f) (.cons (str x) (exp e)))]
  | .dtype l td => node "Dtype" [loc l, typeDef td]
  | .dtabbrev l ns n t => node "Dtabbrev" [loc l, list (ns.map str), str n, type t]
  | .dexn l n ts => node "Dexn" [loc l, str n, list (ts.map type)]
  | .dmod n ds => node "Dmod" [str n, list (ds.map dec)]
  | .dlocal a b => node "Dlocal" [list (a.map dec), list (b.map dec)]
  | .denv n => node "Denv" [str n]

def program (ds : List Dec) : Sexp := list (ds.map dec)
end Flapjack.CakeParser.ToSexp
