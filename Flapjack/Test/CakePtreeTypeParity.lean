import Flapjack.CakeParser.PtreeConversion
import Flapjack.CakeParser.PegEval

/-! Parse and convert the type captured from the pinned HOL parser and
`ptree_Type`; this exercises the actual generated grammar and conversion. -/
namespace Flapjack.Test.CakePtreeTypeParity
open Flapjack.CakeParser Flapjack.CakeParser.PegEval Flapjack.CakeParser.PtreeConversion
open Flapjack.Basis.Pure.MlString Flapjack.Misc.Location

private def loc (a b : Nat) : Locs := .locs (.posn 0 a) (.posn 0 b)
private def input : List (Token × Locs) :=
  [(.tyvarT (ofString "'a"), loc 0 2), (.arrowT, loc 3 5),
   (.alphaT (ofString "int"), loc 6 9), (.alphaT (ofString "list"), loc 10 14)]

#guard match eval 400 (.nt (.inl .nType) .id) input with
  | .success [tree] [] => match ptreeType .nType tree with
    | some (.atfun (.atvar a) (.atapp [.atapp [] (.short intName)] (.short listName))) =>
        a == ofString "'a" && intName == ofString "int" && listName == ofString "list"
    | _ => false
  | _ => false

private def abbrevInput : List (Token × Locs) :=
  [(.typeT, loc 0 4), (.tyvarT (ofString "'a"), loc 5 7),
   (.alphaT (ofString "box"), loc 8 11), (.equalsT, loc 12 13),
   (.tyvarT (ofString "'a"), loc 14 16), (.alphaT (ofString "list"), loc 17 21)]

#guard match eval 400 (.nt (.inl .nTypeAbbrevDec) .id) abbrevInput with
  | .success [tree] [] => match ptreeTypeAbbrevDec tree with
    | some (.dtabbrev span [v] name (.atapp [.atvar a] (.short listName))) =>
        span == loc 0 21 && v == ofString "'a" && name == ofString "box" &&
        a == ofString "'a" && listName == ofString "list"
    | _ => false
  | _ => false

end Flapjack.Test.CakePtreeTypeParity
