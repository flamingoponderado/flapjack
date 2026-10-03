import Flapjack.Misc.BalancedMap.Invariants
import Mathlib.Tactic.NormNum

namespace Flapjack.Test.BalancedMapInvariants
open Misc.BalancedMap

-- bmv_structure_size_0
example : structureSize (κ := Nat) (ν := Nat) .tip = 0 := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_invariant_0
example : invariant (κ := Nat) (ν := Nat) compare .tip := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_key_ordered_0
example : keyOrdered (κ := Nat) (ν := Nat) compare 10 .tip .gt := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_structure_size_1
example : structureSize (κ := Nat) (ν := Nat) (.bin 1 10 100 .tip .tip) = 1 := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_invariant_1
example : invariant (κ := Nat) (ν := Nat) compare (.bin 1 10 100 .tip .tip) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_key_ordered_1
example : ¬ (keyOrdered (κ := Nat) (ν := Nat) compare 10 (.bin 1 10 100 .tip .tip) .gt) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]
  all_goals decide

-- bmv_structure_size_2
example : structureSize (κ := Nat) (ν := Nat) (.bin 0 10 100 .tip .tip) = 1 := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_invariant_2
example : ¬ (invariant (κ := Nat) (ν := Nat) compare (.bin 0 10 100 .tip .tip)) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_key_ordered_2
example : ¬ (keyOrdered (κ := Nat) (ν := Nat) compare 10 (.bin 0 10 100 .tip .tip) .gt) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]
  all_goals decide

-- bmv_structure_size_3
example : structureSize (κ := Nat) (ν := Nat) (.bin 3 10 100 (.bin 1 5 50 .tip .tip) (.bin 1 15 150 .tip .tip)) = 3 := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_invariant_3
example : invariant (κ := Nat) (ν := Nat) compare (.bin 3 10 100 (.bin 1 5 50 .tip .tip) (.bin 1 15 150 .tip .tip)) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]
  all_goals decide

-- bmv_key_ordered_3
example : ¬ (keyOrdered (κ := Nat) (ν := Nat) compare 10 (.bin 3 10 100 (.bin 1 5 50 .tip .tip) (.bin 1 15 150 .tip .tip)) .gt) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]
  all_goals decide

-- bmv_structure_size_4
example : structureSize (κ := Nat) (ν := Nat) (.bin 3 10 100 (.bin 1 15 150 .tip .tip) (.bin 1 5 50 .tip .tip)) = 3 := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_invariant_4
example : ¬ (invariant (κ := Nat) (ν := Nat) compare (.bin 3 10 100 (.bin 1 15 150 .tip .tip) (.bin 1 5 50 .tip .tip))) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_key_ordered_4
example : ¬ (keyOrdered (κ := Nat) (ν := Nat) compare 10 (.bin 3 10 100 (.bin 1 15 150 .tip .tip) (.bin 1 5 50 .tip .tip)) .gt) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]
  all_goals decide

-- bmv_structure_size_5
example : structureSize (κ := Nat) (ν := Nat) (.bin 3 10 100 (.bin 1 10 100 .tip .tip) (.bin 1 15 150 .tip .tip)) = 3 := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_invariant_5
example : ¬ (invariant (κ := Nat) (ν := Nat) compare (.bin 3 10 100 (.bin 1 10 100 .tip .tip) (.bin 1 15 150 .tip .tip))) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]
  all_goals decide

-- bmv_key_ordered_5
example : ¬ (keyOrdered (κ := Nat) (ν := Nat) compare 10 (.bin 3 10 100 (.bin 1 10 100 .tip .tip) (.bin 1 15 150 .tip .tip)) .gt) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]
  all_goals decide

-- bmv_structure_size_6
example : structureSize (κ := Nat) (ν := Nat) (.bin 4 10 100 (.bin 2 5 50 (.bin 1 3 30 .tip .tip) .tip) (.bin 1 15 150 .tip .tip)) = 4 := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_invariant_6
example : invariant (κ := Nat) (ν := Nat) compare (.bin 4 10 100 (.bin 2 5 50 (.bin 1 3 30 .tip .tip) .tip) (.bin 1 15 150 .tip .tip)) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]
  all_goals decide

-- bmv_key_ordered_6
example : ¬ (keyOrdered (κ := Nat) (ν := Nat) compare 10 (.bin 4 10 100 (.bin 2 5 50 (.bin 1 3 30 .tip .tip) .tip) (.bin 1 15 150 .tip .tip)) .gt) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]
  all_goals decide

-- bmv_structure_size_7
example : structureSize (κ := Nat) (ν := Nat) (.bin 4 10 100 (.bin 2 5 50 .tip (.bin 1 12 120 .tip .tip)) (.bin 1 15 150 .tip .tip)) = 4 := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_invariant_7
example : ¬ (invariant (κ := Nat) (ν := Nat) compare (.bin 4 10 100 (.bin 2 5 50 .tip (.bin 1 12 120 .tip .tip)) (.bin 1 15 150 .tip .tip))) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]
  all_goals decide

-- bmv_key_ordered_7
example : ¬ (keyOrdered (κ := Nat) (ν := Nat) compare 10 (.bin 4 10 100 (.bin 2 5 50 .tip (.bin 1 12 120 .tip .tip)) (.bin 1 15 150 .tip .tip)) .gt) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]
  all_goals decide

-- bmv_structure_size_8
example : structureSize (κ := Nat) (ν := Nat) (.bin 2 10 100 (.bin 1 5 50 .tip .tip) .tip) = 2 := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_invariant_8
example : invariant (κ := Nat) (ν := Nat) compare (.bin 2 10 100 (.bin 1 5 50 .tip .tip) .tip) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]
  all_goals decide

-- bmv_key_ordered_8
example : ¬ (keyOrdered (κ := Nat) (ν := Nat) compare 10 (.bin 2 10 100 (.bin 1 5 50 .tip .tip) .tip) .gt) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]
  all_goals decide

-- bmv_structure_size_9
example : structureSize (κ := Nat) (ν := Nat) (.bin 3 10 100 (.bin 2 5 50 (.bin 1 3 30 .tip .tip) .tip) .tip) = 3 := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_invariant_9
example : ¬ (invariant (κ := Nat) (ν := Nat) compare (.bin 3 10 100 (.bin 2 5 50 (.bin 1 3 30 .tip .tip) .tip) .tip)) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]

-- bmv_key_ordered_9
example : ¬ (keyOrdered (κ := Nat) (ν := Nat) compare 10 (.bin 3 10 100 (.bin 2 5 50 (.bin 1 3 30 .tip .tip) .tip) .tip) .gt) := by
  norm_num [invariant, keyOrdered, balanced, size, structureSize, delta, compare]
  all_goals decide

example : balanced 0 0 := by norm_num [balanced, delta]
example : balanced 0 1 := by norm_num [balanced, delta]
example : ¬ (balanced 0 2) := by norm_num [balanced, delta]
example : balanced 1 3 := by norm_num [balanced, delta]
example : ¬ (balanced 1 4) := by norm_num [balanced, delta]
example : balanced 2 6 := by norm_num [balanced, delta]
example : ¬ (balanced 2 7) := by norm_num [balanced, delta]

def runChecks : IO Bool := do
  IO.println "BalancedMapInvariants: 37 original predicate kernel fixtures checked"
  return true

end Flapjack.Test.BalancedMapInvariants
