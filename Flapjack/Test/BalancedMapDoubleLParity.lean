import Flapjack.Misc.BalancedMap.RotationCorrect.DoubleL
import Flapjack.Misc.BalancedMap.LookupSemantics

namespace Flapjack.Test.BalancedMapDoubleLParity
open Flapjack.Misc.BalancedMap
noncomputable section
local instance : DecidableEq (Set (Fin 3)) := Classical.typeDecidableEq _
private def cmp (x y : Fin 3) : Ordering := compare x.val y.val
private theorem good : Flapjack.FiniteMap.Comparison.goodCmp cmp := by
  unfold Flapjack.FiniteMap.Comparison.goodCmp cmp
  decide
private def last : Map (Fin 3) Nat := .tip
private def middle : Map (Fin 3) Nat := .bin 1 1 10 .tip .tip
private def right : Map (Fin 3) Nat := .bin 2 2 20 middle last
private theorem premises :
    Flapjack.FiniteMap.Comparison.goodCmp cmp ∧ keyOrdered cmp 0 right .lt ∧
    keyOrdered cmp 0 (.tip : Map (Fin 3) Nat) .gt ∧ almostBalancedR (size (.tip : Map (Fin 3) Nat)) 2 ∧
    ¬ (2 + size (.tip : Map (Fin 3) Nat) ≤ 1) ∧
    2 > delta * size (.tip : Map (Fin 3) Nat) ∧
    ¬ (size middle < ratio * size last) ∧
    invariant cmp right ∧ invariant cmp (.tip : Map (Fin 3) Nat) := by
  refine ⟨good, ?_⟩
  simp [right, last, middle, keyOrdered, almostBalancedR, invariant, structureSize,
    size, balanced, cmp, delta, ratio]
  decide
private theorem full : invariant cmp (doubleL 0 0 .tip right) ∧
    toFmap cmp (doubleL 0 0 .tip right) =
    ((toFmap cmp .tip).union (toFmap cmp right)).updateEq (keySet cmp 0, 0) :=
  doubleLThm 0 0 .tip cmp 2 2 20 middle last premises
example : doubleL 0 0 .tip right =
    .bin 3 1 10 (.bin 1 0 0 .tip .tip) (.bin 1 2 20 .tip .tip) := by
  rw [right, middle, doubleLDef]
  rfl
example : invariant cmp (doubleL 0 0 .tip right) := full.1
example : toFmap cmp (doubleL 0 0 .tip right) =
    ((toFmap cmp .tip).union (toFmap cmp right)).updateEq (keySet cmp 0, 0) := full.2
example : (toFmap cmp (doubleL 0 0 .tip right)).lookup (keySet cmp 0) = some 0 := by
  calc
    _ = lookup cmp 0 (doubleL 0 0 .tip right) :=
      (lookupThm cmp 0 _ ⟨good, full.1⟩).symm
    _ = some 0 := by rw [right, middle, doubleLDef]; rfl
example : (toFmap cmp (doubleL 0 0 .tip right)).lookup (keySet cmp 1) = some 10 := by
  calc
    _ = lookup cmp 1 (doubleL 0 0 .tip right) :=
      (lookupThm cmp 1 _ ⟨good, full.1⟩).symm
    _ = some 10 := by rw [right, middle, doubleLDef]; rfl
example : (toFmap cmp (doubleL 0 0 .tip right)).lookup (keySet cmp 2) = some 20 := by
  calc
    _ = lookup cmp 2 (doubleL 0 0 .tip right) :=
      (lookupThm cmp 2 _ ⟨good, full.1⟩).symm
    _ = some 20 := by rw [right, middle, doubleLDef]; rfl
end
end Flapjack.Test.BalancedMapDoubleLParity
