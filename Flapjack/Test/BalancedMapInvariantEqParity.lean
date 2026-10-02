import Flapjack.Misc.BalancedMap.InvariantSemantics

namespace Flapjack.Test.BalancedMapInvariantEqParity
open Flapjack.Misc.BalancedMap

private def cmp (x y : Nat) : Ordering :=
  if x < y then .lt else if x = y then .eq else .gt

example : invariant cmp (.bin 1 4 99 .tip .tip) := by
  simp [invariant, structureSize, keyOrdered, balanced, size]
example : ¬ invariant cmp (.bin 0 4 99 .tip .tip) := by
  simp [invariant, structureSize]
example : ¬ invariant cmp (.bin 2 4 99 (.bin 1 4 7 .tip .tip) .tip) := by
  simp [invariant, keyOrdered, cmp]

/-- The Tip conjunct retains its own independent HOL payload type. -/
example {κ β ν : Type} (compare : κ → κ → Ordering)
    (n : Nat) (key : κ) (value : ν) (left right : Map κ ν) :
    invariant compare (.tip : Map κ β) ↔ True :=
  (invariantEq (β := β) compare n key value left right).1

end Flapjack.Test.BalancedMapInvariantEqParity
