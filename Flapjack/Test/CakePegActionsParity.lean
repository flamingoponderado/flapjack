import Flapjack.CakeParser.PegActions

/-! Replay the semantic-action trees and locations from pinned HOL. -/
namespace Flapjack.Test.CakePegActionsParity
open Flapjack.CakeParser Flapjack.CakeParser.PegActions
open Flapjack.Basis.Pure.MlString Flapjack.Misc.Location

private def l (a b : Nat) : Locs := .locs (.posn 0 a) (.posn 0 b)
private def a : ParseTree := .leaf (.inr (.intT 1)) (l 1 2)
private def b : ParseTree := .leaf (.inr (.intT 2)) (l 5 6)
private def b4 : ParseTree := .leaf (.inr (.intT 2)) (l 4 5)
private def plus : ParseTree := .leaf (.inr (.symbolT (ofString "+"))) (l 3 4)
private def comma : ParseTree := .leaf (.inr .commaT) (l 3 4)

#guard evalUnary (.bindNT (.inl .nE)) [a, b4] ==
  [.node (.inl .nE) (l 1 5) [a, b4]]
#guard evalBinary (.mkLinfix (.inl .nEadd)) [a] [plus, b] ==
  [.node (.inl .nEadd) (l 1 6) [.node (.inl .nEadd) (l 1 2) [a], plus, b]]
#guard [evalBinary .foldEapp [a] [b], evalBinary .foldDType [a] [b],
    evalBinary .pappCtor [a] [b], evalBinary .ebaseParen [a, b, comma, b, a] []] ==
  [[.node (.inl .nEapp) (l 1 6) [.node (.inl .nEapp) (l 1 2) [a], b]],
   [.node (.inl .nDType) (l 1 6) [.node (.inl .nDType) (l 1 2) [a], b]],
   [.node (.inl .nPapp) (l 1 6) [.node (.inl .nPConApp) (l 1 2) [a], b]],
   [.node (.inl .nEbase) (l 1 2) [.node (.inl .nEtuple) (l 1 2)
     [a, .node (.inl .nElist2) (l 5 6) [b, comma, b], a]]]]

end Flapjack.Test.CakePegActionsParity
