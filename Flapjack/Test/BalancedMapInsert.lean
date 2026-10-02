import Flapjack.Misc.BalancedMap.Insert

namespace Flapjack.Test.BalancedMapInsert
open Misc.BalancedMap

-- Complete original HOL outputs, independently captured before kernel checks.
-- bmi_0_3
example : insert (κ := Nat) (ν := Nat) compare 3 777 .tip = (.bin 1 3 777 .tip .tip) := by decide

-- bmi_0_10
example : insert (κ := Nat) (ν := Nat) compare 10 777 .tip = (.bin 1 10 777 .tip .tip) := by decide

-- bmi_0_17
example : insert (κ := Nat) (ν := Nat) compare 17 777 .tip = (.bin 1 17 777 .tip .tip) := by decide

-- bmi_1_3
example : insert (κ := Nat) (ν := Nat) compare 3 777 (.bin 99 10 100 .tip .tip) = (.bin 2 10 100 (.bin 1 3 777 .tip .tip) .tip) := by decide

-- bmi_1_10
example : insert (κ := Nat) (ν := Nat) compare 10 777 (.bin 99 10 100 .tip .tip) = (.bin 99 10 777 .tip .tip) := by decide

-- bmi_1_17
example : insert (κ := Nat) (ν := Nat) compare 17 777 (.bin 99 10 100 .tip .tip) = (.bin 2 10 100 .tip (.bin 1 17 777 .tip .tip)) := by decide

-- bmi_2_3
example : insert (κ := Nat) (ν := Nat) compare 3 777 (.bin 0 10 100 (.bin 90 20 200 .tip .tip) (.bin 80 5 50 .tip .tip)) = (.bin 83 10 100 (.bin 2 20 200 (.bin 1 3 777 .tip .tip) .tip) (.bin 80 5 50 .tip .tip)) := by decide

-- bmi_2_10
example : insert (κ := Nat) (ν := Nat) compare 10 777 (.bin 0 10 100 (.bin 90 20 200 .tip .tip) (.bin 80 5 50 .tip .tip)) = (.bin 0 10 777 (.bin 90 20 200 .tip .tip) (.bin 80 5 50 .tip .tip)) := by decide

-- bmi_2_17
example : insert (κ := Nat) (ν := Nat) compare 17 777 (.bin 0 10 100 (.bin 90 20 200 .tip .tip) (.bin 80 5 50 .tip .tip)) = (.bin 93 10 100 (.bin 90 20 200 .tip .tip) (.bin 2 5 50 .tip (.bin 1 17 777 .tip .tip))) := by decide

-- bmi_3_3
example : insert (κ := Nat) (ν := Nat) compare 3 777 (.bin 3 10 100 (.bin 1 5 50 .tip .tip) (.bin 1 15 150 .tip .tip)) = (.bin 4 10 100 (.bin 2 5 50 (.bin 1 3 777 .tip .tip) .tip) (.bin 1 15 150 .tip .tip)) := by decide

-- bmi_3_10
example : insert (κ := Nat) (ν := Nat) compare 10 777 (.bin 3 10 100 (.bin 1 5 50 .tip .tip) (.bin 1 15 150 .tip .tip)) = (.bin 3 10 777 (.bin 1 5 50 .tip .tip) (.bin 1 15 150 .tip .tip)) := by decide

-- bmi_3_17
example : insert (κ := Nat) (ν := Nat) compare 17 777 (.bin 3 10 100 (.bin 1 5 50 .tip .tip) (.bin 1 15 150 .tip .tip)) = (.bin 4 10 100 (.bin 1 5 50 .tip .tip) (.bin 2 15 150 .tip (.bin 1 17 777 .tip .tip))) := by decide

-- bmi_4_3
example : insert (κ := Nat) (ν := Nat) compare 3 777 (.bin 9 10 100 (.bin 8 5 50 (.bin 7 3 30 .tip .tip) .tip) (.bin 1 15 150 .tip .tip)) = (.bin 4 10 100 (.bin 2 5 50 (.bin 7 3 777 .tip .tip) .tip) (.bin 1 15 150 .tip .tip)) := by decide

-- bmi_4_10
example : insert (κ := Nat) (ν := Nat) compare 10 777 (.bin 9 10 100 (.bin 8 5 50 (.bin 7 3 30 .tip .tip) .tip) (.bin 1 15 150 .tip .tip)) = (.bin 9 10 777 (.bin 8 5 50 (.bin 7 3 30 .tip .tip) .tip) (.bin 1 15 150 .tip .tip)) := by decide

-- bmi_4_17
example : insert (κ := Nat) (ν := Nat) compare 17 777 (.bin 9 10 100 (.bin 8 5 50 (.bin 7 3 30 .tip .tip) .tip) (.bin 1 15 150 .tip .tip)) = (.bin 11 10 100 (.bin 8 5 50 (.bin 7 3 30 .tip .tip) .tip) (.bin 2 15 150 .tip (.bin 1 17 777 .tip .tip))) := by decide

-- bmi_equal_distinct
example : insert (κ := Nat) (ν := Nat) (fun _ _ => Ordering.eq) 999 888 (.bin 0 10 100 (.bin 90 20 200 .tip .tip) (.bin 80 5 50 .tip .tip)) = (.bin 0 999 888 (.bin 90 20 200 .tip .tip) (.bin 80 5 50 .tip .tip)) := by decide

example {κ ν : Type} (cmp : κ → κ → Ordering) (key oldKey : κ) (value oldValue : ν) (n : Nat) (left right : Map κ ν) (h : cmp key oldKey = .eq) :
    insert cmp key value (.bin n oldKey oldValue left right) = .bin n key value left right := by
  simp only [Flapjack.Misc.BalancedMap.insert.eq_2, h]

def runChecks : IO Bool := do
  IO.println "BalancedMapInsert: 16 original complete-tree fixtures and universal equal-key replacement checked"
  return true

end Flapjack.Test.BalancedMapInsert
