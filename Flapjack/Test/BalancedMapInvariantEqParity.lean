import Flapjack.Misc.BalancedMap.InvariantSemantics
import Flapjack.Misc.BalancedMap.LookupSemantics

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

example {κ ν : Type} (compare : κ → κ → Ordering) (key : κ) (tree : Map κ ν)
    (h : Flapjack.FiniteMap.Comparison.goodCmp compare ∧ invariant compare tree) :
    lookup compare key tree = (toFmap compare tree).lookup (keySet compare key) :=
  lookupThm compare key tree h

example : (toFmap cmp3 (.bin 3 1 99 left3 right3)).lookup (keySet cmp3 0) = some 7 := by
  rw [← lookupThm cmp3 0 _ ⟨goodCmp3, inv3⟩]
  rfl
example : (toFmap cmp3 (.bin 3 1 99 left3 right3)).lookup (keySet cmp3 1) = some 99 := by
  rw [← lookupThm cmp3 1 _ ⟨goodCmp3, inv3⟩]
  rfl
example : (toFmap cmp3 (.bin 3 1 99 left3 right3)).lookup (keySet cmp3 2) = some 8 := by
  rw [← lookupThm cmp3 2 _ ⟨goodCmp3, inv3⟩]
  rfl
example : (toFmap cmp3 left3).lookup (keySet cmp3 2) = none := by
  rw [← lookupThm cmp3 2 _ ⟨goodCmp3, inv3.2.2.2.2.1⟩]
  rfl
example : lookup cmp 3
    (.bin 3 1 99 (.bin 1 0 7 .tip .tip) (.bin 1 2 8 .tip .tip)) = none := rfl
example : lookup (fun (_ _ : Bool) => Ordering.eq)
    true (.bin 1 false 11 .tip .tip : Map Bool Nat) = some 11 := rfl

example : (toFmap (fun (_ _ : Bool) => Ordering.eq)
    (.bin 1 false "equivalent" .tip .tip)).lookup
      (keySet (fun (_ _ : Bool) => Ordering.eq) true) = some "equivalent" := by
  rw [← lookupThm _ true _]
  · rfl
  · constructor
    · unfold Flapjack.FiniteMap.Comparison.goodCmp
      decide
    · simp [invariant, structureSize, keyOrdered, balanced, size]

end Flapjack.Test.BalancedMapInvariantEqParity
