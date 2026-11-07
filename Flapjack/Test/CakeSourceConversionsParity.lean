import Flapjack.SemanticPrimitivesHOL.Conversions

/-! Source value-encoding observations captured from pinned HOL. -/
namespace Flapjack.Test.CakeSourceConversionsParity
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

private def intV (n : Int) : Value := .litv (.intLit n)
private def charV (n : HolChar) : Value := .litv (.char n)
private def wordV (n : BitVec 8) : Value := .litv (.word8 n)

#guard match valueToList (listToValue [intV 1, intV 2]) with
  | some [.litv (.intLit 1), .litv (.intLit 2)] => true
  | _ => false
#guard (valueToList (.conv (some (.typeStamp (ofString "wrong") 1)) [])).isNone
#guard valueToCharList (listToValue [charV 97, charV 98]) = some [97, 98]
#guard valuesToString [.litv (.strLit (ofString "a")), .litv (.strLit (ofString "b"))] = some (ofString "ab")
#guard valueToId (.conv (some (.typeStamp (ofString "Long") 4)) [.litv (.strLit (ofString "M")),
    .conv (some (.typeStamp (ofString "Short") 4)) [.litv (.strLit (ofString "x"))]]) =
  some (.long (ofString "M") (.short (ofString "x")))
#guard valueToWord8List (listToValue [wordV 3, wordV 7]) = some [3, 7]
#guard (valueToWord8List (listToValue [wordV 3, intV 7])).isNone

end Flapjack.Test.CakeSourceConversionsParity
