import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapAppend
namespace Flapjack.Test.WordToStackBitmapAppendParity
open Flapjack.StackSem Flapjack.WordToStackProofs
example : readBitmap (width := 8) [13] ≠ none ∧
    readBitmap (width := 8) ([13] ++ [255]) = readBitmap (width := 8) [13] := by cbv; simp
example : readBitmap (width := 8) [128,3] ≠ none ∧
    readBitmap (width := 8) ([128,3] ++ [255]) = readBitmap (width := 8) [128,3] := by cbv; simp
example : fullReadBitmap (bitmapWidth := 8) (width := 8) [3] (.word 1) ≠ none ∧
    fullReadBitmap (bitmapWidth := 8) (width := 8) ([3] ++ [255]) (.word 1) = fullReadBitmap (bitmapWidth := 8) (width := 8) [3] (.word 1) := by cbv; simp
example : fullReadBitmap (bitmapWidth := 8) (width := 8) [0,3] (.word 2) ≠ none ∧
    fullReadBitmap (bitmapWidth := 8) (width := 8) ([0,3] ++ [255]) (.word 2) = fullReadBitmap (bitmapWidth := 8) (width := 8) [0,3] (.word 2) := by cbv; simp

def runChecks : IO Bool := do
  IO.println "PASS exact Word-to-Stack bitmap append matches four original HOL rows"
  pure true
end Flapjack.Test.WordToStackBitmapAppendParity
