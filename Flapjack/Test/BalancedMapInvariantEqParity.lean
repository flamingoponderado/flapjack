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

example : invariant cmp
    (.bin 3 1 99 (.bin 1 0 7 .tip .tip) (.bin 1 2 8 .tip .tip)) := by
  simp [invariant, structureSize, keyOrdered, balanced, size, cmp, delta]

private def cmp3 (x y : Fin 3) : Ordering := compare x.val y.val
private theorem goodCmp3 : Flapjack.FiniteMap.Comparison.goodCmp cmp3 := by
  unfold Flapjack.FiniteMap.Comparison.goodCmp cmp3
  decide

private def left3 : Map (Fin 3) Nat := .bin 1 0 7 .tip .tip
private def right3 : Map (Fin 3) Nat := .bin 1 2 8 .tip .tip
private theorem inv3 : invariant cmp3 (.bin 3 1 99 left3 right3) := by
  simp only [invariant, left3, right3, structureSize, keyOrdered, size, cmp3, balanced]
  decide

example : Disjoint {keys | (toFmap cmp3 left3).lookup keys ≠ none}
    {keys | (toFmap cmp3 right3).lookup keys ≠ none} :=
  (invProps cmp3 3 1 99 left3 right3 ⟨goodCmp3, inv3⟩).1

example : cmp3 1 0 = .gt := by
  apply (invProps cmp3 3 1 99 left3 right3 ⟨goodCmp3, inv3⟩).2.1 0
  simp [left3, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

example : cmp3 1 2 = .lt := by
  apply (invProps cmp3 3 1 99 left3 right3 ⟨goodCmp3, inv3⟩).2.2 2
  simp [right3, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

end Flapjack.Test.BalancedMapInvariantEqParity
