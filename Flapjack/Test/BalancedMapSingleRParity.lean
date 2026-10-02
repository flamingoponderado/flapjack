import Flapjack.Misc.BalancedMap.RotationCorrect.SingleR
import Flapjack.Misc.BalancedMap.LookupSemantics

namespace Flapjack.Test.BalancedMapSingleRParity
open Flapjack.Misc.BalancedMap
noncomputable section
local instance : DecidableEq (Set (Fin 3)) := Classical.typeDecidableEq _
private def cmp (x y : Fin 3) : Ordering := compare x.val y.val
private theorem good : Flapjack.FiniteMap.Comparison.goodCmp cmp := by
  unfold Flapjack.FiniteMap.Comparison.goodCmp cmp
  decide
private def first : Map (Fin 3) Nat := .bin 1 0 0 .tip .tip
private def left : Map (Fin 3) Nat := .bin 2 1 10 first .tip
private theorem premises :
    Flapjack.FiniteMap.Comparison.goodCmp cmp ∧ keyOrdered cmp 2 left .gt ∧
    keyOrdered cmp 2 (.tip : Map (Fin 3) Nat) .lt ∧ almostBalancedL 2 (size (.tip : Map (Fin 3) Nat)) ∧
    ¬ (size (.tip : Map (Fin 3) Nat) + 2 ≤ 1) ∧
    2 > delta * size (.tip : Map (Fin 3) Nat) ∧
    size (.tip : Map (Fin 3) Nat) < ratio * size first ∧
    invariant cmp left ∧ invariant cmp (.tip : Map (Fin 3) Nat) := by
  refine ⟨good, ?_⟩
  simp [left, first, keyOrdered, almostBalancedL, invariant, structureSize,
    size, balanced, cmp, delta, ratio]
  decide
private theorem full : invariant cmp (singleR 2 20 left .tip) ∧
    toFmap cmp (singleR 2 20 left .tip) =
    ((toFmap cmp left).union (toFmap cmp .tip)).updateEq (keySet cmp 2, 20) :=
  singleRThm 2 20 .tip cmp 2 1 10 first .tip premises
example : singleR 2 20 left .tip =
    .bin 3 1 10 first (.bin 1 2 20 .tip .tip) := by
  rw [left, singleRDef]
  rfl
example : invariant cmp (singleR 2 20 left .tip) := full.1
example : toFmap cmp (singleR 2 20 left .tip) =
    ((toFmap cmp left).union (toFmap cmp .tip)).updateEq (keySet cmp 2, 20) := full.2
example : (toFmap cmp (singleR 2 20 left .tip)).lookup (keySet cmp 0) = some 0 := by
  calc
    _ = lookup cmp 0 (singleR 2 20 left .tip) :=
      (lookupThm cmp 0 _ ⟨good, full.1⟩).symm
    _ = some 0 := by rw [left, singleRDef]; rfl
example : (toFmap cmp (singleR 2 20 left .tip)).lookup (keySet cmp 1) = some 10 := by
  calc
    _ = lookup cmp 1 (singleR 2 20 left .tip) :=
      (lookupThm cmp 1 _ ⟨good, full.1⟩).symm
    _ = some 10 := by rw [left, singleRDef]; rfl
example : (toFmap cmp (singleR 2 20 left .tip)).lookup (keySet cmp 2) = some 20 := by
  calc
    _ = lookup cmp 2 (singleR 2 20 left .tip) :=
      (lookupThm cmp 2 _ ⟨good, full.1⟩).symm
    _ = some 20 := by rw [left, singleRDef]; rfl
end
end Flapjack.Test.BalancedMapSingleRParity
