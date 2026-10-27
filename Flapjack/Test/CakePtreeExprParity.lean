import Flapjack.CakeParser.PtreeConversion
import Flapjack.CakeParser.PegEval

/-! Replay complete expression trees and source annotations from pinned HOL. -/
namespace Flapjack.Test.CakePtreeExprParity
open Flapjack.CakeParser Flapjack.CakeParser.PegEval Flapjack.CakeParser.PtreeConversion
open Flapjack.Basis.Pure.MlString Flapjack.Misc.Location

private def loc (a b : Nat) : Locs := .locs (.posn 0 a) (.posn 0 b)
private def functionInput : List (Token × Locs) :=
  [(.fnT, loc 0 2), (.alphaT (ofString "x"), loc 3 4),
   (.darrowT, loc 5 7), (.alphaT (ofString "x"), loc 8 9)]

#guard match eval 500 (.nt (.inl .nE) .id) functionInput with
  | .success [tree] [] => match ptreeExpr .nE tree with
    | some (.lannot (.fn x (.lannot (.var (.short y)) inner)) outer) =>
      x == ofString "x" && y == ofString "x" && inner == loc 8 9 && outer == loc 0 9
    | _ => false
  | _ => false

private def letInput : List (Token × Locs) :=
  [(.letT, loc 0 3), (.valT, loc 4 7), (.alphaT (ofString "x"), loc 8 9),
   (.equalsT, loc 10 11), (.intT 1, loc 12 13), (.inT, loc 14 16),
   (.alphaT (ofString "x"), loc 17 18), (.symbolT (ofString "+"), loc 19 20),
   (.intT 2, loc 21 22), (.endT, loc 23 26)]

#guard match eval 500 (.nt (.inl .nE) .id) letInput with
  | .success [tree] [] => match ptreeExpr .nE tree with
    | some (.lannot (.let_ (some x) (.lannot (.lit (.intLit 1)) l1)
        (.lannot (.app .opapp [.app .opapp [.var (.short op),
          .lannot (.var (.short y)) ly], .lannot (.lit (.intLit 2)) l2]) lb)) outer) =>
      x == ofString "x" && y == ofString "x" && op == ofString "+" &&
      l1 == loc 12 13 && ly == loc 17 18 && l2 == loc 21 22 &&
      lb == loc 17 22 && outer == loc 0 26
    | _ => false
  | _ => false

private def caseInput : List (Token × Locs) :=
  [(.caseT, loc 0 4), (.alphaT (ofString "x"), loc 5 6), (.ofT, loc 7 9),
   (.alphaT (ofString "y"), loc 10 11), (.darrowT, loc 12 14),
   (.alphaT (ofString "y"), loc 15 16)]

#guard match eval 500 (.nt (.inl .nE) .id) caseInput with
  | .success [tree] [] => match ptreeExpr .nE tree with
    | some (.lannot (.mat (.lannot (.var (.short x)) lx)
        [(.pvar p, .lannot (.var (.short y)) ly)]) outer) =>
      x == ofString "x" && p == ofString "y" && y == ofString "y" &&
      lx == loc 5 6 && ly == loc 15 16 && outer == .locs (.posn 0 0) .unknownPt
    | _ => false
  | _ => false

end Flapjack.Test.CakePtreeExprParity
