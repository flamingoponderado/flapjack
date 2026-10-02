import Flapjack.Misc.BalancedMap.Rotations

namespace Flapjack.Test.BalancedMapRotations
open Misc.BalancedMap

-- Full output trees transcribed from original HOL, not computed by Lean.
-- bml_0
example : balanceL (κ := Nat) (ν := Nat) 1 10 .tip .tip = (.bin 1 1 10 .tip .tip) := by decide

-- bml_1
example : balanceL (κ := Nat) (ν := Nat) 1 10 (.bin 99 2 20 .tip .tip) .tip = (.bin 2 1 10 (.bin 99 2 20 .tip .tip) .tip) := by decide

-- bml_2
example : balanceL (κ := Nat) (ν := Nat) 1 10 (.bin 88 2 20 .tip (.bin 4 4 40 (.bin 11 5 50 .tip .tip) (.bin 13 6 60 .tip .tip))) .tip = (.bin 3 4 40 (.bin 1 2 20 .tip .tip) (.bin 1 1 10 .tip .tip)) := by decide

-- bml_3
example : balanceL (κ := Nat) (ν := Nat) 1 10 (.bin 88 2 20 (.bin 4 4 40 (.bin 11 5 50 .tip .tip) (.bin 13 6 60 .tip .tip)) .tip) .tip = (.bin 3 2 20 (.bin 4 4 40 (.bin 11 5 50 .tip .tip) (.bin 13 6 60 .tip .tip)) (.bin 1 1 10 .tip .tip)) := by decide

-- bml_4
example : balanceL (κ := Nat) (ν := Nat) 1 10 (.bin 30 2 20 (.bin 5 2 20 .tip .tip) (.bin 9 3 30 .tip .tip)) .tip = (.bin 31 2 20 (.bin 5 2 20 .tip .tip) (.bin 10 1 10 (.bin 9 3 30 .tip .tip) .tip)) := by decide

-- bml_5
example : balanceL (κ := Nat) (ν := Nat) 1 10 (.bin 30 2 20 (.bin 5 2 20 .tip .tip) (.bin 10 3 30 (.bin 11 5 50 .tip .tip) (.bin 13 6 60 .tip .tip))) .tip = (.bin 31 3 30 (.bin 17 2 20 (.bin 5 2 20 .tip .tip) (.bin 11 5 50 .tip .tip)) (.bin 14 1 10 (.bin 13 6 60 .tip .tip) .tip)) := by decide

-- bml_6
example : balanceL (κ := Nat) (ν := Nat) 1 10 .tip (.bin 77 9 90 .tip .tip) = (.bin 78 1 10 .tip (.bin 77 9 90 .tip .tip)) := by decide

-- bml_7
example : balanceL (κ := Nat) (ν := Nat) 1 10 (.bin 3 2 20 .tip .tip) (.bin 1 9 90 .tip .tip) = (.bin 5 1 10 (.bin 3 2 20 .tip .tip) (.bin 1 9 90 .tip .tip)) := by decide

-- bml_8
example : balanceL (κ := Nat) (ν := Nat) 1 10 (.bin 4 2 20 .tip .tip) (.bin 1 9 90 .tip .tip) = .tip := by decide

-- bml_9
example : balanceL (κ := Nat) (ν := Nat) 1 10 (.bin 20 2 20 (.bin 5 2 20 .tip .tip) (.bin 9 3 30 .tip .tip)) (.bin 1 9 90 .tip .tip) = (.bin 22 2 20 (.bin 5 2 20 .tip .tip) (.bin 11 1 10 (.bin 9 3 30 .tip .tip) (.bin 1 9 90 .tip .tip))) := by decide

-- bml_10
example : balanceL (κ := Nat) (ν := Nat) 1 10 (.bin 20 2 20 (.bin 5 2 20 .tip .tip) (.bin 10 3 30 (.bin 11 5 50 .tip .tip) (.bin 13 6 60 .tip .tip))) (.bin 1 9 90 .tip .tip) = (.bin 22 3 30 (.bin 17 2 20 (.bin 5 2 20 .tip .tip) (.bin 11 5 50 .tip .tip)) (.bin 15 1 10 (.bin 13 6 60 .tip .tip) (.bin 1 9 90 .tip .tip))) := by decide

-- bml_11
example : balanceL (κ := Nat) (ν := Nat) 1 10 (.bin 20 2 20 .tip (.bin 7 3 30 .tip .tip)) (.bin 1 9 90 .tip .tip) = .tip := by decide

-- bml_12
example : balanceL (κ := Nat) (ν := Nat) 1 10 (.bin 20 2 20 (.bin 5 2 20 .tip .tip) .tip) (.bin 1 9 90 .tip .tip) = .tip := by decide

-- bml_13
example : balanceL (κ := Nat) (ν := Nat) 1 10 (.bin 20 2 20 .tip .tip) (.bin 1 9 90 .tip .tip) = .tip := by decide

-- bmr_0
example : balanceR (κ := Nat) (ν := Nat) 1 10 .tip .tip = (.bin 1 1 10 .tip .tip) := by decide

-- bmr_1
example : balanceR (κ := Nat) (ν := Nat) 1 10 .tip (.bin 99 2 20 .tip .tip) = (.bin 2 1 10 .tip (.bin 99 2 20 .tip .tip)) := by decide

-- bmr_2
example : balanceR (κ := Nat) (ν := Nat) 1 10 .tip (.bin 88 2 20 .tip (.bin 4 4 40 (.bin 11 5 50 .tip .tip) (.bin 13 6 60 .tip .tip))) = (.bin 3 2 20 (.bin 1 1 10 .tip .tip) (.bin 4 4 40 (.bin 11 5 50 .tip .tip) (.bin 13 6 60 .tip .tip))) := by decide

-- bmr_3
example : balanceR (κ := Nat) (ν := Nat) 1 10 .tip (.bin 88 2 20 (.bin 4 4 40 (.bin 11 5 50 .tip .tip) (.bin 13 6 60 .tip .tip)) .tip) = (.bin 3 4 40 (.bin 1 1 10 .tip .tip) (.bin 1 2 20 .tip .tip)) := by decide

-- bmr_4
example : balanceR (κ := Nat) (ν := Nat) 1 10 .tip (.bin 30 2 20 (.bin 5 2 20 .tip .tip) (.bin 9 3 30 .tip .tip)) = (.bin 31 2 20 (.bin 6 1 10 .tip (.bin 5 2 20 .tip .tip)) (.bin 9 3 30 .tip .tip)) := by decide

-- bmr_5
example : balanceR (κ := Nat) (ν := Nat) 1 10 .tip (.bin 30 2 20 (.bin 5 2 20 .tip .tip) (.bin 10 3 30 (.bin 11 5 50 .tip .tip) (.bin 13 6 60 .tip .tip))) = (.bin 31 2 20 (.bin 6 1 10 .tip (.bin 5 2 20 .tip .tip)) (.bin 10 3 30 (.bin 11 5 50 .tip .tip) (.bin 13 6 60 .tip .tip))) := by decide

-- bmr_6
example : balanceR (κ := Nat) (ν := Nat) 1 10 (.bin 77 9 90 .tip .tip) .tip = (.bin 78 1 10 (.bin 77 9 90 .tip .tip) .tip) := by decide

-- bmr_7
example : balanceR (κ := Nat) (ν := Nat) 1 10 (.bin 1 9 90 .tip .tip) (.bin 3 2 20 .tip .tip) = (.bin 5 1 10 (.bin 1 9 90 .tip .tip) (.bin 3 2 20 .tip .tip)) := by decide

-- bmr_8
example : balanceR (κ := Nat) (ν := Nat) 1 10 (.bin 1 9 90 .tip .tip) (.bin 4 2 20 .tip .tip) = .tip := by decide

-- bmr_9
example : balanceR (κ := Nat) (ν := Nat) 1 10 (.bin 1 9 90 .tip .tip) (.bin 20 2 20 (.bin 5 2 20 .tip .tip) (.bin 9 3 30 .tip .tip)) = (.bin 22 2 20 (.bin 7 1 10 (.bin 1 9 90 .tip .tip) (.bin 5 2 20 .tip .tip)) (.bin 9 3 30 .tip .tip)) := by decide

-- bmr_10
example : balanceR (κ := Nat) (ν := Nat) 1 10 (.bin 1 9 90 .tip .tip) (.bin 20 2 20 (.bin 5 2 20 .tip .tip) (.bin 10 3 30 (.bin 11 5 50 .tip .tip) (.bin 13 6 60 .tip .tip))) = (.bin 22 2 20 (.bin 7 1 10 (.bin 1 9 90 .tip .tip) (.bin 5 2 20 .tip .tip)) (.bin 10 3 30 (.bin 11 5 50 .tip .tip) (.bin 13 6 60 .tip .tip))) := by decide

-- bmr_11
example : balanceR (κ := Nat) (ν := Nat) 1 10 (.bin 1 9 90 .tip .tip) (.bin 20 2 20 .tip (.bin 7 3 30 .tip .tip)) = .tip := by decide

-- bmr_12
example : balanceR (κ := Nat) (ν := Nat) 1 10 (.bin 1 9 90 .tip .tip) (.bin 20 2 20 (.bin 5 2 20 .tip .tip) .tip) = .tip := by decide

-- bmr_13
example : balanceR (κ := Nat) (ν := Nat) 1 10 (.bin 1 9 90 .tip .tip) (.bin 20 2 20 .tip .tip) = .tip := by decide

def runChecks : IO Bool := do
  IO.println "BalancedMapRotations: 28 original complete-tree kernel fixtures checked"
  return true

end Flapjack.Test.BalancedMapRotations
