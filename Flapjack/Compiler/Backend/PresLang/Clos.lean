import Flapjack.Compiler.Backend.PresLang.Flat
import Flapjack.Compiler.Backend.ClosLang.Syntax
import Flapjack.Compiler.Backend.ClosToBvl.Names
import Flapjack.Misc.Sptree

/-! Closure-language explorer presentation, following the `clos_*_to_display`
definitions in `cakeml/compiler/backend/presLangScript.sml`. It is untagged
because the shared display tree uses String-backed names rather than HOL
`mlstring`, and byte encoding correspondence is not yet proved. The explorer
driver does not yet execute this module. -/
namespace Flapjack.Compiler.Backend.PresLang.Clos

open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend

private def text (s : MlString) : DisplayExpr := .string (Source.byteString s)
private def item (name : String) (xs : List DisplayExpr) : DisplayExpr := .item none name xs
private def number (n : Nat) : DisplayExpr := .string (toString n)
private def integer (n : Int) : DisplayExpr := .string (Source.integerText n)
private def boolean (b : Bool) : DisplayExpr := .string (if b then "True" else "False")
private def optional (f : α → DisplayExpr) : Option α → DisplayExpr
  | none => .string "none"
  | some x => item "some" [f x]
private def traced (t : BackendCommon.Tra) (name : String) (xs : List DisplayExpr) : DisplayExpr :=
  .item (some (Flat.trace t)) name xs

/-- Spreadsheet-style names used for de Bruijn indices: a, ..., z, aa, ... . -/
def varName (n : Nat) : String :=
  let last := String.singleton (Char.ofNat (97 + n % 26))
  if n < 26 then last else varName (n / 26 - 1) ++ last
termination_by n
decreasing_by omega

private def varDisplay (n : Nat) : DisplayExpr := .string (varName n)
private def varNames (base count : Nat) : List DisplayExpr :=
  (List.range count).reverse.map (fun i => varDisplay (base + i + 1))

/-- Render optional code labels using CakeML's sparse name table. -/
def attachName (names : Spt MlString) : Option Nat → String
  | none => "none"
  | some n => match sptLookup n names with
    | none => toString n
    | some s => Source.byteString s ++ "@" ++ toString n

private def constPart : ClosLang.ConstPart → DisplayExpr
  | .int n => item "Int" [integer n]
  | .con n ns => item "Con" [number n, .tuple (ns.map number)]
  | .str s => item "Str" [.string ("\"" ++ Source.byteString s ++ "\"")]
  | .w64 w => item "W64" [wordToDisplay w]

private def constant : ClosLang.Const → DisplayExpr
  | .constInt n => item "ConstInt" [integer n]
  | .constCons n cs => item "ConstCons" [number n, .tuple (cs.map constant)]
  | .constStr s => item "ConstStr" [.string ("\"" ++ Source.byteString s ++ "\"")]
  | .constWord64 w => item "ConstWord64" [wordToDisplay w]

private def block : ClosLang.BlockOp → DisplayExpr
  | .cons n => item "Cons" [number n] | .elemAt n => item "ElemAt" [number n]
  | .tagLenEq n m => item "TagLenEq" [number n, number m]
  | .boolTest t => item "BoolTest" [Source.test t] | .boolNot => .string "BoolNot"
  | .lenEq n => item "LenEq" [number n] | .tagEq n => item "TagEq" [number n]
  | .lengthBlock => .string "LengthBlock" | .boundsCheckBlock => .string "BoundsCheckBlock"
  | .consExtend n => item "ConsExtend" [number n] | .fromList n => item "FromList" [number n]
  | .listAppend => .string "ListAppend" | .constant c => item "Constant" [constant c]
  | .equal => .string "Equal" | .equalConst c => item "EqualConst" [constPart c]
  | .build cs => item "Build" (cs.map constPart)

private def memory : ClosLang.MemOp → DisplayExpr
  | .ref => .string "Ref" | .update => .string "Update" | .el => .string "El"
  | .length => .string "Length" | .lengthByte => .string "LengthByte"
  | .refByte b => item "RefByte" [boolean b] | .refArray => .string "RefArray"
  | .derefByte => .string "DerefByte" | .updateByte => .string "UpdateByte"
  | .concatByteVec => .string "ConcatByteVec" | .copyByte b => item "CopyByte" [boolean b]
  | .fromListByte => .string "FromListByte" | .toListByte => .string "ToListByte"
  | .lengthByteVec => .string "LengthByteVec" | .derefByteVec => .string "DerefByteVec"
  | .boundsCheckArray => .string "BoundsCheckArray"
  | .boundsCheckByte b => item "BoundsCheckByte" [boolean b]
  | .configGC => .string "ConfigGC" | .stringCmp b c => item "StringCmp" [boolean b, Source.comparison c]
  | .xorByte => .string "XorByte" | .mutCons n m => item "MutCons" [number n, number m]
  | .updateCons => .string "UpdateCons" | .finaliseCons => .string "FinaliseCons"

private def intOp : ClosLang.IntOp → DisplayExpr
  | .const i => item "Const" [integer i] | .add => .string "Add" | .sub => .string "Sub"
  | .mult => .string "Mult" | .div => .string "Div" | .mod => .string "Mod"
  | .less => .string "Less" | .lessEq => .string "LessEq"
  | .greater => .string "Greater" | .greaterEq => .string "GreaterEq"
  | .lessConstSmall n => item "LessConstSmall" [number n]

private def opw : BackendCommon.Opw → DisplayExpr
  | .andw => .string "Andw" | .orw => .string "Orw" | .xor => .string "Xor"
  | .add => .string "Add" | .sub => .string "Sub"

private def wordOp : ClosLang.WordOp → DisplayExpr
  | .wordOpw w o => item "WordOp" [Source.wordSize w, opw o]
  | .wordShift w s n => item "WordShift" [Source.wordSize w, Source.shift s, number n]
  | .wordTest w t => item "WordTest" [Source.wordSize w, Source.test t]
  | .wordFromInt => .string "WordFromInt" | .wordToInt => .string "WordToInt"
  | .wordFromWord b => item "WordFromWord" [boolean b]
  | .fpCmp .less => .string "FP_Less" | .fpCmp .lessEqual => .string "FP_LessEqual"
  | .fpCmp .greater => .string "FP_Greater" | .fpCmp .greaterEqual => .string "FP_GreaterEqual"
  | .fpCmp .equal => .string "FP_Equal" | .fpUop .abs => .string "FP_Abs"
  | .fpUop .neg => .string "FP_Neg" | .fpUop .sqrt => .string "FP_Sqrt"
  | .fpBop .add => .string "FP_Add" | .fpBop .sub => .string "FP_Sub"
  | .fpBop .mul => .string "FP_Mul" | .fpBop .div => .string "FP_Div"
  | .fpTop .fma => .string "FP_Fma"

/-- Display all closure operators, including names for known labels. -/
def op (names : Spt MlString) : ClosLang.Op → DisplayExpr
  | .globOp (.global n) => item "Global" [number n]
  | .globOp (.setGlobal n) => item "SetGlobal" [number n]
  | .globOp .allocGlobal => .string "AllocGlobal" | .globOp .globalsPtr => .string "GlobalsPtr"
  | .globOp .setGlobalsPtr => .string "SetGlobalsPtr" | .blockOp b => block b | .memOp m => memory m
  | .label n => item "Label" [.string (attachName names (some n))]
  | .ffi s => item "FFI" [text s] | .intOp i => intOp i | .wordOp w => wordOp w
  | .install => .string "Install" | .thunkOp t => Source.thunk t

mutual
/-- Render closure expressions with the original de Bruijn naming rules. -/
def expression (names : Spt MlString) (height : Nat) : ClosLang.Exp → DisplayExpr
  | .var t n => traced t "var" [varDisplay (height - n - 1)]
  | .ifThenElse t a b c => traced t "if" [expression names height a, expression names height b, expression names height c]
  | .let _ es e => .list [.string "let", .tuple (bindings names height (es.length - 1) es), expression names (height + es.length) e]
  | .raise t e => traced t "raise" [expression names height e]
  | .tick t e => traced t "tick" [expression names height e]
  | .handle t a b => traced t "handle" [expression names height a, varDisplay height, expression names (height + 1) b]
  | .call t ticks dest es => traced t "call" ([number ticks, .string (attachName names (some dest))] ++ es.map (expression names height))
  | .app t arity e es => traced t "app" ([optional number arity, expression names height e] ++ es.map (expression names height))
  | .fn hint loc free arity e => traced .none ("fn<" ++ Source.byteString hint ++ ">")
      [optional number loc, optional (fun ns => .tuple (ns.map number)) free,
       .tuple (varNames height arity), expression names height e]
  | .letrec hints loc free fs e => traced .none ("letrec<" ++ String.intercalate "," (hints.map Source.byteString) ++ ">")
      [optional number loc, optional (fun ns => .tuple (ns.map number)) free,
       .tuple (recursiveBindings names height (fs.length - 1) fs.length fs), expression names height e]
  | .op t o es => traced t "op" (op .ln o :: es.map (expression names height))
termination_by e => sizeOf e

private def bindings (names : Spt MlString) (height index : Nat) : List ClosLang.Exp → List DisplayExpr
  | [] => []
  | e :: es => .tuple [varDisplay (height + index), .string "<-", expression names height e] ::
      bindings names height (index - 1) es
termination_by es => sizeOf es

private def recursiveBindings (names : Spt MlString) (height index len : Nat) :
    List (Nat × ClosLang.Exp) → List DisplayExpr
  | [] => []
  | (arity, e) :: es =>
      .tuple [varDisplay (height + index), .tuple (varNames (height + len - 1) arity),
        expression names (height + len + arity) e] :: recursiveBindings names height (index - 1) len es
termination_by es => sizeOf es
end

private def render (e : DisplayExpr) : List String :=
  displayStrTreeToStrings "\n\n" (displayToStrTree e)

/-- Render closure declarations and named functions in original order. -/
def programs (names : Spt MlString) (decls : List ClosLang.Exp)
    (functions : List (Nat × Nat × ClosLang.Exp)) : List String :=
  mapAppendDisplayStrings (fun e => render (.tuple [.string "dec", expression names 0 e])) decls ++
  mapAppendDisplayStrings (fun (n, arity, body) => render (.tuple [
    .string "func", .string (attachName names (some n)),
    .tuple ((List.range arity).reverse.map varDisplay), expression names arity body])) functions

/-- Convert byte-valued display characters back to the original output bytes. -/
def programBytes (names : Spt MlString) (decls : List ClosLang.Exp)
    (functions : List (Nat × Nat × ClosLang.Exp)) : List HolChar :=
  (programs names decls functions).flatMap fun fragment =>
    fragment.toList.map (fun c => BitVec.ofNat 8 c.toNat)

/-- Compute the source-name table used by the original `clos_to_strs` and
render the declarations followed by functions. -/
def sourcePrograms (decls : List ClosLang.Exp)
    (functions : List (Nat × Nat × ClosLang.Exp)) : List String :=
  let names := ClosToBvl.getSrcNames (decls ++ functions.map (fun (_, _, body) => body)) .ln
  programs names decls functions

end Flapjack.Compiler.Backend.PresLang.Clos
