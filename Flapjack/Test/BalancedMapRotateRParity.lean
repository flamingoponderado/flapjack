import Flapjack.Misc.BalancedMap.RotationCorrect.RotateR
import Flapjack.Misc.BalancedMap.LookupSemantics
namespace Flapjack.Test.BalancedMapRotateRParity
open Flapjack.Misc.BalancedMap
noncomputable section
local instance : DecidableEq (Set (Fin 3)) := Classical.typeDecidableEq _
private def cmp (x y : Fin 3) : Ordering := compare x.val y.val
private theorem good : Flapjack.FiniteMap.Comparison.goodCmp cmp := by
  unfold Flapjack.FiniteMap.Comparison.goodCmp cmp
  decide
private def singleLeft : Map (Fin 3) Nat := .bin 2 1 10 (.bin 1 0 0 .tip .tip) .tip
private def doubleLeft : Map (Fin 3) Nat := .bin 2 0 0 .tip (.bin 1 1 10 .tip .tip)
private def output : Map (Fin 3) Nat :=
  .bin 3 1 10 (.bin 1 0 0 .tip .tip) (.bin 1 2 20 .tip .tip)
private theorem singlePremises :
    Flapjack.FiniteMap.Comparison.goodCmp cmp ∧ keyOrdered cmp 2 singleLeft .gt ∧
    keyOrdered cmp 2 (.tip : Map (Fin 3) Nat) .lt ∧
    ¬ (size singleLeft + size (.tip : Map (Fin 3) Nat) ≤ 1) ∧
    size singleLeft > delta * size (.tip : Map (Fin 3) Nat) ∧
    almostBalancedL (size singleLeft) (size (.tip : Map (Fin 3) Nat)) ∧
    invariant cmp singleLeft ∧ invariant cmp (.tip : Map (Fin 3) Nat) := by
  refine ⟨good, ?_⟩
  simp [singleLeft, keyOrdered, size, delta, almostBalancedL, invariant, structureSize, balanced, cmp]
  decide
private theorem singleFull : invariant cmp (rotateR 2 20 singleLeft .tip) ∧
    toFmap cmp (rotateR 2 20 singleLeft .tip) =
    ((toFmap cmp singleLeft).union (toFmap cmp .tip)).updateEq (keySet cmp 2, 20) :=
  rotateRThm 2 20 singleLeft .tip cmp singlePremises
private theorem singleOutput : rotateR 2 20 singleLeft .tip = output := by
  simp [singleLeft, rotateR, size, ratio, singleRDef, output, bin]
example : invariant cmp (rotateR 2 20 singleLeft .tip) := singleFull.1
example : toFmap cmp (rotateR 2 20 singleLeft .tip) =
    ((toFmap cmp singleLeft).union (toFmap cmp .tip)).updateEq (keySet cmp 2, 20) := singleFull.2
example : (toFmap cmp (rotateR 2 20 singleLeft .tip)).lookup (keySet cmp 0) = some 0 := by
  calc
    _ = lookup cmp 0 (rotateR 2 20 singleLeft .tip) :=
      (lookupThm cmp 0 _ ⟨good, singleFull.1⟩).symm
    _ = some 0 := by rw [singleOutput]; rfl
example : (toFmap cmp (rotateR 2 20 singleLeft .tip)).lookup (keySet cmp 1) = some 10 := by
  calc
    _ = lookup cmp 1 (rotateR 2 20 singleLeft .tip) :=
      (lookupThm cmp 1 _ ⟨good, singleFull.1⟩).symm
    _ = some 10 := by rw [singleOutput]; rfl
example : (toFmap cmp (rotateR 2 20 singleLeft .tip)).lookup (keySet cmp 2) = some 20 := by
  calc
    _ = lookup cmp 2 (rotateR 2 20 singleLeft .tip) :=
      (lookupThm cmp 2 _ ⟨good, singleFull.1⟩).symm
    _ = some 20 := by rw [singleOutput]; rfl
private theorem doublePremises :
    Flapjack.FiniteMap.Comparison.goodCmp cmp ∧ keyOrdered cmp 2 doubleLeft .gt ∧
    keyOrdered cmp 2 (.tip : Map (Fin 3) Nat) .lt ∧
    ¬ (size doubleLeft + size (.tip : Map (Fin 3) Nat) ≤ 1) ∧
    size doubleLeft > delta * size (.tip : Map (Fin 3) Nat) ∧
    almostBalancedL (size doubleLeft) (size (.tip : Map (Fin 3) Nat)) ∧
    invariant cmp doubleLeft ∧ invariant cmp (.tip : Map (Fin 3) Nat) := by
  refine ⟨good, ?_⟩
  simp [doubleLeft, keyOrdered, size, delta, almostBalancedL, invariant, structureSize, balanced, cmp]
  decide
private theorem doubleFull : invariant cmp (rotateR 2 20 doubleLeft .tip) ∧
    toFmap cmp (rotateR 2 20 doubleLeft .tip) =
    ((toFmap cmp doubleLeft).union (toFmap cmp .tip)).updateEq (keySet cmp 2, 20) :=
  rotateRThm 2 20 doubleLeft .tip cmp doublePremises
private theorem doubleOutput : rotateR 2 20 doubleLeft .tip = output := by
  simp [doubleLeft, rotateR, size, ratio, doubleRDef, output, bin]
example : invariant cmp (rotateR 2 20 doubleLeft .tip) := doubleFull.1
example : toFmap cmp (rotateR 2 20 doubleLeft .tip) =
    ((toFmap cmp doubleLeft).union (toFmap cmp .tip)).updateEq (keySet cmp 2, 20) := doubleFull.2
example : (toFmap cmp (rotateR 2 20 doubleLeft .tip)).lookup (keySet cmp 0) = some 0 := by
  calc
    _ = lookup cmp 0 (rotateR 2 20 doubleLeft .tip) :=
      (lookupThm cmp 0 _ ⟨good, doubleFull.1⟩).symm
    _ = some 0 := by rw [doubleOutput]; rfl
example : (toFmap cmp (rotateR 2 20 doubleLeft .tip)).lookup (keySet cmp 1) = some 10 := by
  calc
    _ = lookup cmp 1 (rotateR 2 20 doubleLeft .tip) :=
      (lookupThm cmp 1 _ ⟨good, doubleFull.1⟩).symm
    _ = some 10 := by rw [doubleOutput]; rfl
example : (toFmap cmp (rotateR 2 20 doubleLeft .tip)).lookup (keySet cmp 2) = some 20 := by
  calc
    _ = lookup cmp 2 (rotateR 2 20 doubleLeft .tip) :=
      (lookupThm cmp 2 _ ⟨good, doubleFull.1⟩).symm
    _ = some 20 := by rw [doubleOutput]; rfl
end
end Flapjack.Test.BalancedMapRotateRParity
