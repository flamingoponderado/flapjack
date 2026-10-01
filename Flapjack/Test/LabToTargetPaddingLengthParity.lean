import Flapjack.Compiler.Backend.LabToTarget.PaddingLength

namespace Flapjack.Test.LabToTargetPaddingLengthParity
open Flapjack.Compiler.Backend.LabToTarget

-- Direct original HOL EVAL observations, including the empty-nop sentinel
-- outside LENGTH_pad_bytes's nonempty premise.
example : padBytes [1, 2] 5 [9] = [1, 2, 9, 9, 9] := by decide +kernel
example : padBytes [1] 6 [8, 9] = [1, 8, 9, 8, 9, 8] := by decide +kernel
example : padBytes [1, 2] 2 [9] = [1, 2] := by decide +kernel
example : padBytes ([] : List Nat) 0 [9] = [] := by decide +kernel
example : padBytes [true] 4 [false, true] = [true, false, true, false] := by decide +kernel
example : padBytes ([] : List Nat) 3 [] = [] := by decide +kernel

-- Public theorem exercised at an arbitrary carrier and both branch bounds.
example {α : Type} (bytes nop : List α) (n : Nat)
    (h : 0 < nop.length ∧ bytes.length ≤ n) :
    (padBytes bytes n nop).length = n := lengthPadBytes bytes nop n h

def runChecks : IO Bool := do
  IO.println "PASS exact generic LENGTH_pad_bytes and six original padding observations"
  pure true
end Flapjack.Test.LabToTargetPaddingLengthParity
