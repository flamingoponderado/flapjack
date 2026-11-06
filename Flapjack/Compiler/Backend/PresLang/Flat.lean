import Flapjack.Compiler.Backend.PresLang.Source
import Flapjack.Compiler.Backend.FlatLang

/-! The flat-language explorer printer, following `presLangScript.sml`'s
`opt_con_to_display_def`, `flat_pat_to_display_def`,
`flat_op_to_display_def`, `flat_to_display_def`, and `flat_to_strs_def`.
This code is not tagged as a HOL port: `DisplayExpr` uses Lean strings in
place of HOL `mlstring`, and the byte encoding correspondence remains to be
proved. It is not yet connected to the explorer driver. -/
namespace Flapjack.Compiler.Backend.PresLang.Flat

open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend

private def text (s : MlString) : DisplayExpr := .string (Source.byteString s)
private def item (name : String) (children : List DisplayExpr) : DisplayExpr :=
  .item none name children
private def number (n : Nat) : DisplayExpr := .string (toString n)

/-- Retain the source trace, including its `None` constructor, in display
items. The plain-text renderer intentionally ignores traces. -/
def trace : BackendCommon.Tra → DisplayTrace
  | .none => .none
  | .sourceLoc a b c d => .sourceLoc a b c d
  | .cons t n => .cons (trace t) n
  | .union a b => .union (trace a) (trace b)

private def traced (t : BackendCommon.Tra) (name : String)
    (children : List DisplayExpr) : DisplayExpr :=
  .item (some (trace t)) name children

/-- Constructor identifiers carry an optional type number. -/
def constructor : Option (Nat × Option Nat) → DisplayExpr
  | none => .string "ConIdNone"
  | some (c, none) => item "ConIdUntyped" [number c]
  | some (c, some t) => item "ConIdTyped" [number c, number t]

/-- The original pattern printer omits constructor identifiers. -/
def pattern : FlatLang.Pat → DisplayExpr
  | .pvar n => item "Pvar" [text n]
  | .pany => .string "Pany"
  | .plit l => item "Plit" [Source.literal l]
  | .pcon _ ps => item "Pcon" (ps.map pattern)
  | .pas p n => item "Pas" [pattern p, text n]
  | .pref p => item "Pref" [pattern p]

/-- Display flat-language operators with their numeric operands. -/
def op : FlatLang.Op → DisplayExpr
  | .src o => Source.op o
  | .globalVarAlloc n => item "GlobalVarAlloc" [number n]
  | .globalVarInit n => item "GlobalVarInit" [number n]
  | .globalVarLookup n => item "GlobalVarLookup" [number n]
  | .tagLenEq n m => item "TagLenEq" [number n, number m]
  | .lenEq n => item "LenEq" [number n]
  | .el n => item "El" [number n]
  | .id => .string "Id"

private def optionName : Option MlString → DisplayExpr
  | none => .string "none"
  | some n => item "some" [text n]

mutual
/-- Display a flat expression and its nested cases and function bodies. -/
def expression : FlatLang.Exp → DisplayExpr
  | .raise t e => traced t "raise" [expression e]
  | .handle t e cases => traced t "handle" (expression e :: clauses cases)
  | .lit t _ => traced t "lit" []
  | .con t id es => traced t "con" (constructor id :: es.map expression)
  | .varLocal t n => traced t "var_local" [text n]
  | .fn hint n e => traced .none ("fun<" ++ Source.byteString hint ++ ">") [text n, expression e]
  | .app t o es => traced t "app" (op o :: es.map expression)
  | .if_ t a b c => traced t "if" [expression a, expression b, expression c]
  | .mat t e cases => traced t "mat" (expression e :: clauses cases)
  | .let_ t n a b => traced t "let" [optionName n, expression a, expression b]
  | .letrec hint fs e => traced .none ("letrec<" ++ Source.byteString hint ++ ">")
      [.tuple (functions fs), expression e]
termination_by e => sizeOf e

private def clauses : List (FlatLang.Pat × FlatLang.Exp) → List DisplayExpr
  | [] => []
  | (p, e) :: rest => .tuple [pattern p, expression e] :: clauses rest
termination_by xs => sizeOf xs

private def functions : List (MlString × MlString × FlatLang.Exp) → List DisplayExpr
  | [] => []
  | (m, n, e) :: rest => .tuple [text m, text n, expression e] :: functions rest
termination_by xs => sizeOf xs
end

/-- Render the flat stage using CakeML's per-expression separators. -/
def expressions (es : List FlatLang.Exp) : List String :=
  mapAppendDisplayStrings (fun e => displayStrTreeToStrings "\n\n" (displayToStrTree (expression e))) es

/-- Convert byte-valued display characters back to the original output bytes. -/
def expressionBytes (es : List FlatLang.Exp) : List HolChar :=
  (expressions es).flatMap fun fragment =>
    fragment.toList.map (fun c => BitVec.ofNat 8 c.toNat)

end Flapjack.Compiler.Backend.PresLang.Flat
