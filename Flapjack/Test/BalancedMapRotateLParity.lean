import Flapjack.Misc.BalancedMap.RotationCorrect.RotateL
import Flapjack.Misc.BalancedMap.LookupSemantics
namespace Flapjack.Test.BalancedMapRotateLParity
open Flapjack.Misc.BalancedMap
noncomputable section
local instance : DecidableEq (Set (Fin 3)) := Classical.typeDecidableEq _
private def cmp (x y : Fin 3) : Ordering := compare x.val y.val
private theorem good : Flapjack.FiniteMap.Comparison.goodCmp cmp := by
  unfold Flapjack.FiniteMap.Comparison.goodCmp cmp
  decide
private def singleRight : Map (Fin 3) Nat := .bin 2 1 10 .tip (.bin 1 2 20 .tip .tip)
private def doubleRight : Map (Fin 3) Nat := .bin 2 2 20 (.bin 1 1 10 .tip .tip) .tip
private def output : Map (Fin 3) Nat :=
  .bin 3 1 10 (.bin 1 0 0 .tip .tip) (.bin 1 2 20 .tip .tip)
private theorem singlePremises :
    Flapjack.FiniteMap.Comparison.goodCmp cmp ∧ keyOrdered cmp 0 singleRight .lt ∧
    keyOrdered cmp 0 (.tip : Map (Fin 3) Nat) .gt ∧
    ¬ (size (.tip : Map (Fin 3) Nat) + size singleRight ≤ 1) ∧
    size singleRight > delta * size (.tip : Map (Fin 3) Nat) ∧
    almostBalancedR (size (.tip : Map (Fin 3) Nat)) (size singleRight) ∧
    invariant cmp (.tip : Map (Fin 3) Nat) ∧ invariant cmp singleRight := by
  refine ⟨good, ?_⟩
  simp [singleRight, keyOrdered, size, delta, almostBalancedR, invariant, structureSize, balanced, cmp]
  decide
private theorem singleFull : invariant cmp (rotateL 0 0 .tip singleRight) ∧
    toFmap cmp (rotateL 0 0 .tip singleRight) =
    ((toFmap cmp .tip).union (toFmap cmp singleRight)).updateEq (keySet cmp 0, 0) :=
  rotateLThm 0 0 .tip singleRight cmp singlePremises
private theorem singleOutput : rotateL 0 0 .tip singleRight = output := by
  simp [singleRight, rotateL, size, ratio, singleLDef, output, bin]
example : invariant cmp (rotateL 0 0 .tip singleRight) := singleFull.1
example : toFmap cmp (rotateL 0 0 .tip singleRight) =
    ((toFmap cmp .tip).union (toFmap cmp singleRight)).updateEq (keySet cmp 0, 0) := singleFull.2
example : (toFmap cmp (rotateL 0 0 .tip singleRight)).lookup (keySet cmp 0) = some 0 := by
  calc
    _ = lookup cmp 0 (rotateL 0 0 .tip singleRight) :=
      (lookupThm cmp 0 _ ⟨good, singleFull.1⟩).symm
    _ = some 0 := by rw [singleOutput]; rfl
example : (toFmap cmp (rotateL 0 0 .tip singleRight)).lookup (keySet cmp 1) = some 10 := by
  calc
    _ = lookup cmp 1 (rotateL 0 0 .tip singleRight) :=
      (lookupThm cmp 1 _ ⟨good, singleFull.1⟩).symm
    _ = some 10 := by rw [singleOutput]; rfl
example : (toFmap cmp (rotateL 0 0 .tip singleRight)).lookup (keySet cmp 2) = some 20 := by
  calc
    _ = lookup cmp 2 (rotateL 0 0 .tip singleRight) :=
      (lookupThm cmp 2 _ ⟨good, singleFull.1⟩).symm
    _ = some 20 := by rw [singleOutput]; rfl
private theorem doublePremises :
    Flapjack.FiniteMap.Comparison.goodCmp cmp ∧ keyOrdered cmp 0 doubleRight .lt ∧
    keyOrdered cmp 0 (.tip : Map (Fin 3) Nat) .gt ∧
    ¬ (size (.tip : Map (Fin 3) Nat) + size doubleRight ≤ 1) ∧
    size doubleRight > delta * size (.tip : Map (Fin 3) Nat) ∧
    almostBalancedR (size (.tip : Map (Fin 3) Nat)) (size doubleRight) ∧
    invariant cmp (.tip : Map (Fin 3) Nat) ∧ invariant cmp doubleRight := by
  refine ⟨good, ?_⟩
  simp [doubleRight, keyOrdered, size, delta, almostBalancedR, invariant, structureSize, balanced, cmp]
  decide
private theorem doubleFull : invariant cmp (rotateL 0 0 .tip doubleRight) ∧
    toFmap cmp (rotateL 0 0 .tip doubleRight) =
    ((toFmap cmp .tip).union (toFmap cmp doubleRight)).updateEq (keySet cmp 0, 0) :=
  rotateLThm 0 0 .tip doubleRight cmp doublePremises
private theorem doubleOutput : rotateL 0 0 .tip doubleRight = output := by
  simp [doubleRight, rotateL, size, ratio, doubleLDef, output, bin]
example : invariant cmp (rotateL 0 0 .tip doubleRight) := doubleFull.1
example : toFmap cmp (rotateL 0 0 .tip doubleRight) =
    ((toFmap cmp .tip).union (toFmap cmp doubleRight)).updateEq (keySet cmp 0, 0) := doubleFull.2
example : (toFmap cmp (rotateL 0 0 .tip doubleRight)).lookup (keySet cmp 0) = some 0 := by
  calc
    _ = lookup cmp 0 (rotateL 0 0 .tip doubleRight) :=
      (lookupThm cmp 0 _ ⟨good, doubleFull.1⟩).symm
    _ = some 0 := by rw [doubleOutput]; rfl
example : (toFmap cmp (rotateL 0 0 .tip doubleRight)).lookup (keySet cmp 1) = some 10 := by
  calc
    _ = lookup cmp 1 (rotateL 0 0 .tip doubleRight) :=
      (lookupThm cmp 1 _ ⟨good, doubleFull.1⟩).symm
    _ = some 10 := by rw [doubleOutput]; rfl
example : (toFmap cmp (rotateL 0 0 .tip doubleRight)).lookup (keySet cmp 2) = some 20 := by
  calc
    _ = lookup cmp 2 (rotateL 0 0 .tip doubleRight) :=
      (lookupThm cmp 2 _ ⟨good, doubleFull.1⟩).symm
    _ = some 20 := by rw [doubleOutput]; rfl
end
end Flapjack.Test.BalancedMapRotateLParity
