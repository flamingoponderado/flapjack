import Flapjack.AstHOL.Syntax
import Flapjack.Display

/-! CakeML source-language presentation for the compiler explorer, following
`cakeml/compiler/backend/presLangScript.sml`'s `id_to_display_def`,
`lit_to_display_def`, `ast_t_to_display_def`, `pat_to_display_def`,
`op_to_display_def`, `exp_to_display_def`, `source_to_display_dec_def`, and
`source_to_strs_def`.

The existing display tree uses Lean strings. `byteString` maps each HOL byte
to the Unicode scalar with the same value, and `declarationBytes` writes those
scalars as individual bytes rather than encoding them as UTF-8.
These definitions are not tagged as HOL ports: their result uses the existing
String-backed `DisplayExpr`/`DisplayStrTree` rather than HOL's `mlstring`
carriers, and the byte encoding has not been proved to preserve those carriers.
The explorer does not yet execute this source-stage printer. -/
namespace Flapjack.Compiler.Backend.PresLang.Source

open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString

/-- Embed each HOL character as the scalar with the same byte value. -/
def byteString (s : MlString) : String :=
  String.ofList (s.explode.map (fun b => Char.ofNat b.toNat))

private def text (s : MlString) : DisplayExpr := .string (byteString s)
private def item (name : String) (children : List DisplayExpr) : DisplayExpr :=
  .item none name children
private def opt (f : α → DisplayExpr) : Option α → DisplayExpr
  | none => .string "none"
  | some x => item "some" [f x]

/-- Display source identifiers, preserving each byte of module and name. -/
def ident : Ident MlString MlString → DisplayExpr
  | .short n => item "Short" [text n]
  | .long n i => item "Long" [text n, ident i]

private def integerText (i : Int) : String :=
  if i < 0 then "~" ++ toString i.natAbs else toString i

/-- Display a source literal, including CakeML's unescaped character form. -/
def literal : Lit → DisplayExpr
  | .intLit n => item "IntLit" [.string (integerText n)]
  | .char c => item "Char" [.string ("#\"" ++ String.singleton (Char.ofNat c.toNat) ++ "\"")]
  | .strLit s => item "StrLit" [text s]
  | .word8 w => item "Word8" [wordToDisplay w]
  | .word64 w => item "Word64" [wordToDisplay w]
  | .float64 w => item "Float64" [wordToDisplay w]

/-- Display a source type annotation. CakeML labels the `Atapp` case
`Attup`; this seemingly surprising spelling is intentional. -/
def astType : AstT → DisplayExpr
  | .atvar n => item "Atvar" [text n]
  | .atfun a b => item "Atfun" [astType a, astType b]
  | .attup ts => item "Attup" [.tuple (ts.map astType)]
  | .atapp ts id => item "Attup" [.tuple (ts.map astType), ident id]

/-- Display a source pattern and its nested constructor arguments. -/
def pattern : Pat → DisplayExpr
  | .pany => item "Pany" []
  | .pvar n => item "Pvar" [text n]
  | .plit l => item "Plit" [literal l]
  | .pcon id ps => item "Pcon" [opt ident id, .tuple (ps.map pattern)]
  | .pas p n => item "Pas" [pattern p, text n]
  | .pref p => item "Pref" [pattern p]
  | .ptannot p t => item "Ptannot" [pattern p, astType t]

private def wordSize : WordSize → DisplayExpr
  | .w8 => .string "W8" | .w64 => .string "W64"

private def primType : PrimType → DisplayExpr
  | .boolT => .string "BoolT" | .intT => .string "IntT"
  | .charT => .string "CharT" | .strT => .string "StrT"
  | .float64T => .string "Float64T"
  | .wordT .w8 => .string "WordT_W8" | .wordT .w64 => .string "WordT_W64"

private def arithmetic : Arith → DisplayExpr
  | .add => .string "Add" | .sub => .string "Sub" | .mul => .string "Mul"
  | .div => .string "Div" | .mod => .string "Mod" | .neg => .string "Neg"
  | .and => .string "And" | .xor => .string "Xor" | .or => .string "Or"
  | .not => .string "Not" | .abs => .string "Abs" | .sqrt => .string "Sqrt"
  | .fma => .string "FMA"

private def comparison : Opb → DisplayExpr
  | .lt => .string "Lt" | .gt => .string "Gt"
  | .leq => .string "Leq" | .geq => .string "Geq"

private def test : Test → DisplayExpr
  | .equal => .string "Equal"
  | .compare c => item "Compare" [comparison c]
  | .altCompare c => item "AltCompare" [comparison c]

private def shift : Shift → DisplayExpr
  | .lsl => .string "Lsl" | .lsr => .string "Lsr"
  | .asr => .string "Asr" | .ror => .string "Ror"

private def thunkMode : ThunkMode → DisplayExpr
  | .evaluated => .string "Evaluated" | .notEvaluated => .string "NotEvaluated"

private def thunk : ThunkOp → DisplayExpr
  | .allocThunk m => item "AllocThunk" [thunkMode m]
  | .updateThunk m => item "UpdateThunk" [thunkMode m]
  | .forceThunk => .string "ForceThunk"

/-- Display source primitives using the original explorer's spellings. -/
def op : Op → DisplayExpr
  | .arith a t => item "Arith" [arithmetic a, primType t]
  | .fromTo a b => item "FromTo" [primType a, primType b]
  | .shift w s n => item "Shift" [wordSize w, shift s, .string (toString n)]
  | .test t ty => item "Test" [test t, primType ty]
  | .equality => .string "Equality" | .opapp => .string "Opapp"
  | .opassign => .string "Opassign" | .opref => .string "Opref"
  | .opderef => .string "Opderef" | .aw8alloc => .string "Aw8alloc"
  | .aw8sub => .string "Aw8sub" | .aw8length => .string "Aw8length"
  | .aw8update => .string "Aw8update" | .copyStrStr => .string "CopyStrStr"
  | .copyStrAw8 => .string "CopyStrAw8" | .copyAw8Str => .string "CopyAw8Str"
  | .copyAw8Aw8 => .string "CopyAw8Aw8" | .xorAw8StrUnsafe => .string "XorAw8Str_unsafe"
  | .implode => .string "Implode" | .explode => .string "Explode"
  | .strsub => .string "Strsub" | .strlen => .string "Strlen" | .strcat => .string "Strcat"
  | .vfromList => .string "VfromList" | .vsub => .string "Vsub"
  | .vlength => .string "Vlength" | .aalloc => .string "Aalloc"
  | .aallocEmpty => .string "AallocEmpty" | .aallocFixed => .string "AallocFixed"
  | .asub => .string "Asub" | .alength => .string "Alength" | .aupdate => .string "Aupdate"
  | .vsubUnsafe => .string "Vsub_unsafe" | .asubUnsafe => .string "Asub_unsafe"
  | .aupdateUnsafe => .string "Aupdate_unsafe" | .aw8subUnsafe => .string "Aw8sub_unsafe"
  | .aw8updateUnsafe => .string "Aw8update_unsafe"
  | .thunkOp t => thunk t | .listAppend => .string "ListAppend"
  | .configGC => .string "ConfigGC" | .ffi _ => .string "FFI v35"
  | .eval => .string "Eval" | .envId => .string "Env_id"

private def logical : Lop → DisplayExpr
  | .andalso => .string "Andalso" | .orelse => .string "Orelse"

mutual
/-- Display a source expression and its pattern and recursive-function lists. -/
def expression : AstHOL.Exp → DisplayExpr
  | .lit l => item "Lit" [literal l]
  | .raise e => item "Raise" [expression e]
  | .con id es => item "Con" [opt ident id, .tuple (es.map expression)]
  | .var id => item "Var" [ident id]
  | .fn n e => item "Fun" [text n, expression e]
  | .app o es => item "App" (op o :: es.map expression)
  | .log o a b => item "Log" [logical o, expression a, expression b]
  | .if_ a b c => item "If" [expression a, expression b, expression c]
  | .let_ n a b => item "Let" [opt text n, expression a, expression b]
  | .mat e cases => item "Mat" [expression e, .tuple (clauses cases)]
  | .handle e cases => item "Handle" [expression e, .tuple (clauses cases)]
  | .letrec fs e => item "Letrec" [.tuple (functions fs), expression e]
  | .tannot e _ => item "Tannot" [expression e]
  | .lannot e _ => item "Lannot" [expression e]
termination_by e => sizeOf e

private def clauses : List (Pat × AstHOL.Exp) → List DisplayExpr
  | [] => []
  | (p, e) :: rest => .tuple [pattern p, expression e] :: clauses rest
termination_by xs => sizeOf xs

private def functions : List (VarN × VarN × AstHOL.Exp) → List DisplayExpr
  | [] => []
  | (m, n, e) :: rest => .tuple [text m, text n, expression e] :: functions rest
termination_by xs => sizeOf xs
end

/-- Display source declarations, ignoring location annotations as in CakeML. -/
def declaration : Dec → DisplayExpr
  | .dlet _ p e => item "Dlet" [pattern p, expression e]
  | .dletrec _ fs => item "Dletrec" (functions fs)
  | .dtype _ ts => item "Dtype" (ts.map (fun (ns, n, ctors) =>
      .tuple [.tuple (ns.map text), text n,
        .tuple (ctors.map (fun (c, tys) => .tuple [text c, .tuple (tys.map astType)]))]))
  | .dtabbrev _ ns n t => item "Dtabbrev" [.tuple (ns.map text), text n, astType t]
  | .dexn _ n ts => item "Dexn" [text n, .tuple (ts.map astType)]
  | .dmod n ds => item "Dmod" [text n, .tuple (ds.map declaration)]
  | .dlocal xs ys => item "Dlocal" [.tuple (xs.map declaration), .tuple (ys.map declaration)]
  | .denv n => item "Denv" [text n]

/-- Source-stage output fragments. Non-ASCII HOL bytes are represented by
characters with the same numeric values. -/
def declarations (ds : List Dec) : List String :=
  mapAppendDisplayStrings (fun d => displayStrTreeToStrings "\n\n" (displayToStrTree (declaration d))) ds

/-- Encode the source-stage fragments as CakeML bytes. The display conversion
above introduces only ASCII characters and scalar values obtained from HOL
bytes, so this reverses `byteString` without applying UTF-8 encoding. -/
def declarationBytes (ds : List Dec) : List HolChar :=
  (declarations ds).flatMap fun fragment =>
    fragment.toList.map (fun c => BitVec.ofNat 8 c.toNat)

end Flapjack.Compiler.Backend.PresLang.Source
