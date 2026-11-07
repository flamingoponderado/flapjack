import Flapjack.CakeParser.PtreeConversion
import Flapjack.CakeParser.PegEval

/-! Replay original PEG plus pattern conversion on list/constructor and
annotated-variable patterns. -/
namespace Flapjack.Test.CakePtreePatternParity
open Flapjack.CakeParser Flapjack.CakeParser.PegEval Flapjack.CakeParser.PtreeConversion
open Flapjack.Basis.Pure.MlString Flapjack.Misc.Location

private def loc (a b : Nat) : Locs := .locs (.posn 0 a) (.posn 0 b)
private def listInput : List (Token × Locs) :=
  [(.lbrackT, loc 0 1), (.alphaT (ofString "x"), loc 1 2), (.commaT, loc 2 3),
   (.alphaT (ofString "Ref"), loc 4 7), (.alphaT (ofString "y"), loc 8 9),
   (.rbrackT, loc 9 10)]

#guard match eval 400 (.nt (.inl .nPattern) .id) listInput with
  | .success [tree] [] => match ptreePattern .nPattern tree with
    | some (.pcon (some (.short c1)) [.pvar x,
        .pcon (some (.short c2)) [.pref (.pvar y), .pcon (some (.short nil)) []]]) =>
      c1 == ofString "::" && c2 == ofString "::" && nil == ofString "[]" &&
      x == ofString "x" && y == ofString "y"
    | _ => false
  | _ => false

private def typedInput : List (Token × Locs) :=
  [(.alphaT (ofString "x"), loc 0 1), (.colonT, loc 2 3),
   (.alphaT (ofString "int"), loc 4 7)]

#guard match eval 400 (.nt (.inl .nPattern) .id) typedInput with
  | .success [tree] [] => match ptreePattern .nPattern tree with
    | some (.ptannot (.pvar x) (.atapp [] (.short t))) =>
      x == ofString "x" && t == ofString "int"
    | _ => false
  | _ => false

private def literalTree (t : Token) : ParseTree :=
  .node (.inl .nEliteral) unknownLoc [.leaf (.inr t) unknownLoc]

#guard match ptreeEliteral (literalTree (.wordT 42)) with
  | some (.lit (.word64 w)) => w == BitVec.ofNat 64 42
  | _ => false
#guard match ptreeEliteral (literalTree (.ffiT (ofString "print"))) with
  | some (.app (.ffi s) []) => s == ofString "print"
  | _ => false

end Flapjack.Test.CakePtreePatternParity
