import Flapjack.Misc.BalancedMap.RotationCorrect.SingleL
import Flapjack.Misc.BalancedMap.LookupSemantics

namespace Flapjack.Test.BalancedMapSingleLParity
open Flapjack.Misc.BalancedMap
noncomputable section
local instance : DecidableEq (Set (Fin 3)) := Classical.typeDecidableEq _
private def cmp (x y : Fin 3) : Ordering := compare x.val y.val
private theorem good : Flapjack.FiniteMap.Comparison.goodCmp cmp := by
  unfold Flapjack.FiniteMap.Comparison.goodCmp cmp
  decide
private def last : Map (Fin 3) Nat := .bin 1 2 20 .tip .tip
private def right : Map (Fin 3) Nat := .bin 2 1 10 .tip last
private theorem premises :
    Flapjack.FiniteMap.Comparison.goodCmp cmp ∧ keyOrdered cmp 0 right .lt ∧
    keyOrdered cmp 0 (.tip : Map (Fin 3) Nat) .gt ∧ almostBalancedR (size (.tip : Map (Fin 3) Nat)) 2 ∧
    ¬ (size (.tip : Map (Fin 3) Nat) + 2 ≤ 1) ∧
    2 > delta * size (.tip : Map (Fin 3) Nat) ∧
    size (.tip : Map (Fin 3) Nat) < ratio * size last ∧
    invariant cmp right ∧ invariant cmp (.tip : Map (Fin 3) Nat) := by
  refine ⟨good, ?_⟩
  simp [right, last, keyOrdered, almostBalancedR, invariant, structureSize,
    size, balanced, cmp, delta, ratio]
  decide
private theorem full : invariant cmp (singleL 0 0 .tip right) ∧
    toFmap cmp (singleL 0 0 .tip right) =
    ((toFmap cmp .tip).union (toFmap cmp right)).updateEq (keySet cmp 0, 0) :=
  singleLThm 0 0 .tip cmp 2 1 10 .tip last premises
example : singleL 0 0 .tip right =
    .bin 3 1 10 (.bin 1 0 0 .tip .tip) last := by
  rw [right, singleLDef]
  rfl
example : invariant cmp (singleL 0 0 .tip right) := full.1
example : toFmap cmp (singleL 0 0 .tip right) =
    ((toFmap cmp .tip).union (toFmap cmp right)).updateEq (keySet cmp 0, 0) := full.2
example : (toFmap cmp (singleL 0 0 .tip right)).lookup (keySet cmp 0) = some 0 := by
  calc
    _ = lookup cmp 0 (singleL 0 0 .tip right) :=
      (lookupThm cmp 0 _ ⟨good, full.1⟩).symm
    _ = some 0 := by rw [right, singleLDef]; rfl
example : (toFmap cmp (singleL 0 0 .tip right)).lookup (keySet cmp 1) = some 10 := by
  calc
    _ = lookup cmp 1 (singleL 0 0 .tip right) :=
      (lookupThm cmp 1 _ ⟨good, full.1⟩).symm
    _ = some 10 := by rw [right, singleLDef]; rfl
example : (toFmap cmp (singleL 0 0 .tip right)).lookup (keySet cmp 2) = some 20 := by
  calc
    _ = lookup cmp 2 (singleL 0 0 .tip right) :=
      (lookupThm cmp 2 _ ⟨good, full.1⟩).symm
    _ = some 20 := by rw [right, singleLDef]; rfl
end
end Flapjack.Test.BalancedMapSingleLParity
