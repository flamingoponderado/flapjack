import Flapjack.CakeParser.FromSexp.Ast

/-! Finite observations from `cake_from_sexp_probe.out`. The decoder and its
carrier have not yet completed source correspondence review. -/
namespace Flapjack.Test.CakeFromSexpParity
open Flapjack.CakeParser.Sexp Flapjack.CakeParser.FromSexp
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.AstHOL
open Flapjack.Misc.Location

private def bytes (s : String) := (ofString s).explode
private def sym (s : String) : Sexp := .sym (bytes s)
private def str (s : String) : Sexp := .str (bytes s)
private def list (xs : List Sexp) : Sexp := xs.foldr .cons (sym "nil")
private def node (name : String) (args : List Sexp) : Sexp := list (sym name :: args)
private def number : Sexp → Option Nat
  | .num n => some n
  | _ => none

example : [decodeControl (bytes "abc"), decodeControl (bytes "\\\\"),
    decodeControl (bytes "\\00"), decodeControl (bytes "\\1F"),
    decodeControl (bytes "\\7F"), decodeControl (bytes "\\FF"),
    decodeControl (bytes "\\20"), decodeControl (bytes "\\5C"),
    decodeControl (bytes "\\1f"), decodeControl (bytes "\\FG"),
    decodeControl (bytes "\\"), decodeControl [31], decodeControl (bytes "x\\00y")] =
    [some (bytes "abc"), some [92], some [0], some [31], some [127], some [255],
     none, none, none, none, none, none, some [120, 0, 121]] := by native_decide

example : [decodeList number (list []), decodeList number (list [.num 1, .num 2, .num 3]),
    decodeList number (.cons (.num 1) (.num 2)), decodeList number (list [str "x"])] =
    [some [], some [1, 2, 3], none, none] := by native_decide

example : [decodeOption number (sym "NONE"), decodeOption number (node "SOME" [.num 5]),
    decodeOption number (node "SOME" [.num 1, .num 2]), decodeOption number (sym "SOME")] =
    [some none, some (some 5), none, none] := by native_decide

example : [decodeIdFuel destString 10 (node "Short" [str "x"]),
    decodeIdFuel destString 10 (node "Long" [str "M", node "Short" [str "x"]]),
    decodeIdFuel destString 10 (node "Long" [str "M", sym "x"])] =
    [some (.short (ofString "x")), some (.long (ofString "M") (.short (ofString "x"))), none] := by native_decide

example : [decodeLiteral (.num 0), decodeLiteral (.num 12), decodeLiteral (str "a\\00b"),
    decodeLiteral (node "-" [.num 0]), decodeLiteral (node "-" [.num 12]),
    decodeLiteral (node "char" [str "z"]), decodeLiteral (node "char" [str "ab"]),
    decodeLiteral (node "word8" [.num 255]), decodeLiteral (node "word8" [.num 256]),
    decodeLiteral (node "word64" [.num 18446744073709551615]),
    decodeLiteral (node "word64" [.num 18446744073709551616]),
    decodeLiteral (node "float64" [.num 42])] =
    [some (.intLit 0), some (.intLit 12), some (.strLit (.implode [97, 0, 98])),
     none, some (.intLit (-12)), some (.char 122), none, some (.word8 255), none,
     some (.word64 18446744073709551615), none, some (.float64 42)] := by native_decide

example : [decodeLoc (list [sym "unk", sym "eof"]),
    decodeLoc (list [list [.num 1, .num 2], list [.num 3, .num 4]]),
    decodeLoc (list [sym "bad", sym "unk"]), decodeLoc (list [.num 1])] =
    [some (.locs .unknownPt .eofPt), some (.locs (.posn 1 2) (.posn 3 4)), none, none] := by native_decide

private def typeCases : Bool := Id.run do
  let a := node "Atvar" [str "a"]
  match decodeTypeFuel 20 a with
  | some (.atvar n) => if n != ofString "a" then return false
  | _ => return false
  match decodeTypeFuel 20 (node "Atfun" [a, node "Attup" [list []]]) with
  | some (.atfun (.atvar n) (.attup [])) => if n != ofString "a" then return false
  | _ => return false
  match decodeTypeFuel 20 (node "Atapp" [list [a], node "Short" [str "list"]]) with
  | some (.atapp [.atvar n] (.short name)) =>
    if n != ofString "a" || name != ofString "list" then return false
  | _ => return false
  return (decodeTypeFuel 20 (node "Atvar" [sym "x"])).isNone

private def patternCases : Bool := Id.run do
  match decodePatternFuel 20 (str "x") with
  | some (.pvar n) => if n != ofString "x" then return false
  | _ => return false
  match decodePatternFuel 20 (node "Pany" []) with
  | some .pany => pure ()
  | _ => return false
  match decodePatternFuel 20 (node "Plit" [.num 42]) with
  | some (.plit (.intLit 42)) => pure ()
  | _ => return false
  match decodePatternFuel 20 (node "Pcon" [sym "NONE", list [str "x", node "Pany" []]]) with
  | some (.pcon none [.pvar n, .pany]) => if n != ofString "x" then return false
  | _ => return false
  match decodePatternFuel 20 (node "Pas" [node "Pref" [str "x"], str "y"]) with
  | some (.pas (.pref (.pvar x)) y) => if x != ofString "x" || y != ofString "y" then return false
  | _ => return false
  match decodePatternFuel 20 (node "Ptannot" [str "x", node "Atvar" [str "a"]]) with
  | some (.ptannot (.pvar x) (.atvar a)) => if x != ofString "x" || a != ofString "a" then return false
  | _ => return false
  return (decodePatternFuel 20 (node "Pany" [.num 1])).isNone

example : typeCases = true ∧ patternCases = true := by native_decide

example : [decodeOp (sym "Equality"), decodeOp (sym "Opapp"), decodeOp (sym "Aw8subunsafe"),
    decodeOp (sym "ForceThunk"), decodeOp (sym "Envid"), decodeOp (.cons (sym "FFI") (str "x\\00y")),
    decodeOp (.cons (sym "AllocThunk") (sym "Evaluated")),
    decodeOp (.cons (sym "UpdateThunk") (sym "NotEvaluated")),
    decodeOp (.cons (sym "Shift64Ror") (.num 123)),
    decodeOp (.cons (sym "Arith") (.cons (sym "Add") (sym "IntT"))),
    decodeOp (.cons (sym "FromTo") (.cons (sym "Word8T") (sym "Word64T"))),
    decodeOp (.cons (sym "Test") (.cons (sym "AltLessEq") (sym "IntT"))),
    decodeOp (node "Arith" [sym "Add", sym "IntT"]), decodeOp (sym "NoSuchOp")] =
    [some .equality, some .opapp, some .aw8subUnsafe, some (.thunkOp .forceThunk), some .envId,
     some (.ffi (.implode [120, 0, 121])), some (.thunkOp (.allocThunk .evaluated)),
     some (.thunkOp (.updateThunk .notEvaluated)), some (.shift .w64 .ror 123),
     some (.arith .add .intT), some (.fromTo (.wordT .w8) (.wordT .w64)),
     some (.test (.altCompare .leq) .intT), none, none] := by native_decide

end Flapjack.Test.CakeFromSexpParity
