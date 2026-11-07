import Flapjack.SemanticPrimitivesHOL.Array

/-! Source array-copy observations captured from pinned HOL. -/
namespace Flapjack.Test.CakeSourceArrayParity
open Flapjack.SemanticPrimitivesHOL

#guard copyArray ([(1 : Nat), 2, 3, 4], 1) 2 none = some [2, 3]
#guard copyArray ([(1 : Nat), 2, 3, 4], 1) 2 (some ([9, 9, 9, 9], 1)) = some [9, 2, 3, 9]
#guard (copyArray ([(1 : Nat)], -1) 1 none).isNone
#guard (copyArray ([(1 : Nat)], 0) (-1) none).isNone
#guard (copyArray ([(1 : Nat), 2], 1) 2 none).isNone
#guard (copyArray ([(1 : Nat), 2], 0) 2 (some ([9], 0))).isNone
#guard (copyArray ([(1 : Nat), 2], 0) 1 (some ([9], -1))).isNone
#guard copyArray ([(1 : Nat), 2], 2) 0 (some ([9], 1)) = some [9]
#guard charsToWords (wordsToChars [0, 255]) = [0, 255]

end Flapjack.Test.CakeSourceArrayParity
