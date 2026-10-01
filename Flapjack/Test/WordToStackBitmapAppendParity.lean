import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapAppend

namespace Flapjack.Test.WordToStackBitmapAppendParity

open Flapjack Flapjack.StackSem
open Flapjack.WordToStackProofs

-- Nine rows replay `word_to_stack_bitmap_append_probe.out` EVAL rows at width 8.
example : readBitmap ([13] : List (BitVec 8)) = some [true, false, true] := by
  decide +kernel
example : readBitmap (([13] : List (BitVec 8)) ++ [0, 5]) = some [true, false, true] := by
  decide +kernel
example : readBitmap ([129, 13] : List (BitVec 8)) =
    some [true, false, false, false, false, false, false, true, false, true] := by
  decide +kernel
example : readBitmap (([129, 13] : List (BitVec 8)) ++ [7]) =
    some [true, false, false, false, false, false, false, true, false, true] := by
  decide +kernel
example : fullReadBitmap ([13] : List (BitVec 8)) (.word (1 : BitVec 8) : WordLocW 8) =
    some [true, false, true] := by
  decide +kernel
example : fullReadBitmap (([13] : List (BitVec 8)) ++ [99]) (.word (1 : BitVec 8) : WordLocW 8) =
    some [true, false, true] := by
  decide +kernel
example : fullReadBitmap ([129, 13] : List (BitVec 8)) (.word (1 : BitVec 8) : WordLocW 8) =
    some [true, false, false, false, false, false, false, true, false, true] := by
  decide +kernel
example : fullReadBitmap (([129, 13] : List (BitVec 8)) ++ [7]) (.word (1 : BitVec 8) : WordLocW 8) =
    some [true, false, false, false, false, false, false, true, false, true] := by
  decide +kernel
example : fullReadBitmap ([13] : List (BitVec 8)) (.loc 0 0 : WordLocW 8) = none := by
  decide +kernel

def runChecks : IO Bool := do
  IO.println "PASS exact Word-to-Stack bitmap append matches nine original HOL rows"
  pure true

end Flapjack.Test.WordToStackBitmapAppendParity
