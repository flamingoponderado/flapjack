import Flapjack.Misc.BalancedMap.RotationCorrect.BalanceRCorrect
import Flapjack.Misc.BalancedMap.LookupSemantics
namespace Flapjack.Test.BalancedMapBalanceRCorrectParity
open Flapjack.Misc.BalancedMap
noncomputable section
local instance : DecidableEq (Set (Fin 7)) := Classical.typeDecidableEq _
private def cmp (x y : Fin 7) : Ordering := compare x.val y.val
private theorem good : Flapjack.FiniteMap.Comparison.goodCmp cmp := by
  unfold Flapjack.FiniteMap.Comparison.goodCmp cmp
  decide
private def emptyLeft : Map (Fin 7) Nat := .tip
private def emptyRight : Map (Fin 7) Nat := .tip
private theorem emptyPremises :
    Flapjack.FiniteMap.Comparison.goodCmp cmp ∧ keyOrdered cmp 1 emptyRight .lt ∧
    keyOrdered cmp 1 emptyLeft .gt ∧ almostBalancedR (size emptyLeft) (size emptyRight) ∧
    invariant cmp emptyLeft ∧ invariant cmp emptyRight := by
  refine ⟨good, ?_⟩
  simp [emptyLeft, emptyRight, keyOrdered, size, almostBalancedR, invariant, balanced]
private theorem emptyFull : invariant cmp (balanceR 1 50 emptyLeft emptyRight) ∧
    toFmap cmp (balanceR 1 50 emptyLeft emptyRight) =
    ((toFmap cmp emptyLeft).union (toFmap cmp emptyRight)).updateEq (keySet cmp 1, 50) :=
  balanceRThm 1 50 emptyLeft emptyRight cmp emptyPremises
example : invariant cmp (balanceR 1 50 emptyLeft emptyRight) := emptyFull.1
example : toFmap cmp (balanceR 1 50 emptyLeft emptyRight) =
    ((toFmap cmp emptyLeft).union (toFmap cmp emptyRight)).updateEq (keySet cmp 1, 50) := emptyFull.2
example : (toFmap cmp (balanceR 1 50 emptyLeft emptyRight)).lookup (keySet cmp 1) = some 50 := by
  calc
    _ = lookup cmp 1 (balanceR 1 50 emptyLeft emptyRight) :=
      (lookupThm cmp 1 _ ⟨good, emptyFull.1⟩).symm
    _ = some 50 := rfl
private def fallbackLeft : Map (Fin 7) Nat := (.bin 1 0 0 .tip .tip)
private def fallbackRight : Map (Fin 7) Nat := (.bin 1 6 6 .tip .tip)
private theorem fallbackPremises :
    Flapjack.FiniteMap.Comparison.goodCmp cmp ∧ keyOrdered cmp 1 fallbackRight .lt ∧
    keyOrdered cmp 1 fallbackLeft .gt ∧ almostBalancedR (size fallbackLeft) (size fallbackRight) ∧
    invariant cmp fallbackLeft ∧ invariant cmp fallbackRight := by
  refine ⟨good, ?_⟩
  simp [fallbackLeft, fallbackRight, keyOrdered, size, almostBalancedR, invariant, structureSize, balanced, delta, cmp]
  all_goals decide
private theorem fallbackFull : invariant cmp (balanceR 1 50 fallbackLeft fallbackRight) ∧
    toFmap cmp (balanceR 1 50 fallbackLeft fallbackRight) =
    ((toFmap cmp fallbackLeft).union (toFmap cmp fallbackRight)).updateEq (keySet cmp 1, 50) :=
  balanceRThm 1 50 fallbackLeft fallbackRight cmp fallbackPremises
example : invariant cmp (balanceR 1 50 fallbackLeft fallbackRight) := fallbackFull.1
example : toFmap cmp (balanceR 1 50 fallbackLeft fallbackRight) =
    ((toFmap cmp fallbackLeft).union (toFmap cmp fallbackRight)).updateEq (keySet cmp 1, 50) := fallbackFull.2
example : (toFmap cmp (balanceR 1 50 fallbackLeft fallbackRight)).lookup (keySet cmp 1) = some 50 := by
  calc
    _ = lookup cmp 1 (balanceR 1 50 fallbackLeft fallbackRight) :=
      (lookupThm cmp 1 _ ⟨good, fallbackFull.1⟩).symm
    _ = some 50 := rfl
private def single_tipLeft : Map (Fin 7) Nat := .tip
private def single_tipRight : Map (Fin 7) Nat := (.bin 3 5 5 (.bin 1 4 4 .tip .tip) (.bin 1 6 6 .tip .tip))
private theorem single_tipPremises :
    Flapjack.FiniteMap.Comparison.goodCmp cmp ∧ keyOrdered cmp 1 single_tipRight .lt ∧
    keyOrdered cmp 1 single_tipLeft .gt ∧ almostBalancedR (size single_tipLeft) (size single_tipRight) ∧
    invariant cmp single_tipLeft ∧ invariant cmp single_tipRight := by
  refine ⟨good, ?_⟩
  simp [single_tipLeft, single_tipRight, keyOrdered, size, almostBalancedR, invariant, structureSize, balanced, delta, cmp]
  all_goals decide
private theorem single_tipFull : invariant cmp (balanceR 1 50 single_tipLeft single_tipRight) ∧
    toFmap cmp (balanceR 1 50 single_tipLeft single_tipRight) =
    ((toFmap cmp single_tipLeft).union (toFmap cmp single_tipRight)).updateEq (keySet cmp 1, 50) :=
  balanceRThm 1 50 single_tipLeft single_tipRight cmp single_tipPremises
example : invariant cmp (balanceR 1 50 single_tipLeft single_tipRight) := single_tipFull.1
example : toFmap cmp (balanceR 1 50 single_tipLeft single_tipRight) =
    ((toFmap cmp single_tipLeft).union (toFmap cmp single_tipRight)).updateEq (keySet cmp 1, 50) := single_tipFull.2
example : (toFmap cmp (balanceR 1 50 single_tipLeft single_tipRight)).lookup (keySet cmp 1) = some 50 := by
  calc
    _ = lookup cmp 1 (balanceR 1 50 single_tipLeft single_tipRight) :=
      (lookupThm cmp 1 _ ⟨good, single_tipFull.1⟩).symm
    _ = some 50 := rfl
private def double_tipLeft : Map (Fin 7) Nat := .tip
private def double_tipRight : Map (Fin 7) Nat := (.bin 4 5 5 (.bin 2 4 4 (.bin 1 3 3 .tip .tip) .tip) (.bin 1 6 6 .tip .tip))
private theorem double_tipPremises :
    Flapjack.FiniteMap.Comparison.goodCmp cmp ∧ keyOrdered cmp 1 double_tipRight .lt ∧
    keyOrdered cmp 1 double_tipLeft .gt ∧ almostBalancedR (size double_tipLeft) (size double_tipRight) ∧
    invariant cmp double_tipLeft ∧ invariant cmp double_tipRight := by
  refine ⟨good, ?_⟩
  simp [double_tipLeft, double_tipRight, keyOrdered, size, almostBalancedR, invariant, structureSize, balanced, delta, cmp]
  all_goals decide
private theorem double_tipFull : invariant cmp (balanceR 1 50 double_tipLeft double_tipRight) ∧
    toFmap cmp (balanceR 1 50 double_tipLeft double_tipRight) =
    ((toFmap cmp double_tipLeft).union (toFmap cmp double_tipRight)).updateEq (keySet cmp 1, 50) :=
  balanceRThm 1 50 double_tipLeft double_tipRight cmp double_tipPremises
example : invariant cmp (balanceR 1 50 double_tipLeft double_tipRight) := double_tipFull.1
example : toFmap cmp (balanceR 1 50 double_tipLeft double_tipRight) =
    ((toFmap cmp double_tipLeft).union (toFmap cmp double_tipRight)).updateEq (keySet cmp 1, 50) := double_tipFull.2
example : (toFmap cmp (balanceR 1 50 double_tipLeft double_tipRight)).lookup (keySet cmp 1) = some 50 := by
  calc
    _ = lookup cmp 1 (balanceR 1 50 double_tipLeft double_tipRight) :=
      (lookupThm cmp 1 _ ⟨good, double_tipFull.1⟩).symm
    _ = some 50 := rfl
private def heavy_singleLeft : Map (Fin 7) Nat := (.bin 1 0 0 .tip .tip)
private def heavy_singleRight : Map (Fin 7) Nat := (.bin 4 4 4 (.bin 1 3 3 .tip .tip) (.bin 2 5 5 .tip (.bin 1 6 6 .tip .tip)))
private theorem heavy_singlePremises :
    Flapjack.FiniteMap.Comparison.goodCmp cmp ∧ keyOrdered cmp 1 heavy_singleRight .lt ∧
    keyOrdered cmp 1 heavy_singleLeft .gt ∧ almostBalancedR (size heavy_singleLeft) (size heavy_singleRight) ∧
    invariant cmp heavy_singleLeft ∧ invariant cmp heavy_singleRight := by
  refine ⟨good, ?_⟩
  simp [heavy_singleLeft, heavy_singleRight, keyOrdered, size, almostBalancedR, invariant, structureSize, balanced, delta, cmp]
  all_goals decide
private theorem heavy_singleFull : invariant cmp (balanceR 1 50 heavy_singleLeft heavy_singleRight) ∧
    toFmap cmp (balanceR 1 50 heavy_singleLeft heavy_singleRight) =
    ((toFmap cmp heavy_singleLeft).union (toFmap cmp heavy_singleRight)).updateEq (keySet cmp 1, 50) :=
  balanceRThm 1 50 heavy_singleLeft heavy_singleRight cmp heavy_singlePremises
example : invariant cmp (balanceR 1 50 heavy_singleLeft heavy_singleRight) := heavy_singleFull.1
example : toFmap cmp (balanceR 1 50 heavy_singleLeft heavy_singleRight) =
    ((toFmap cmp heavy_singleLeft).union (toFmap cmp heavy_singleRight)).updateEq (keySet cmp 1, 50) := heavy_singleFull.2
example : (toFmap cmp (balanceR 1 50 heavy_singleLeft heavy_singleRight)).lookup (keySet cmp 1) = some 50 := by
  calc
    _ = lookup cmp 1 (balanceR 1 50 heavy_singleLeft heavy_singleRight) :=
      (lookupThm cmp 1 _ ⟨good, heavy_singleFull.1⟩).symm
    _ = some 50 := rfl
private def heavy_doubleLeft : Map (Fin 7) Nat := (.bin 1 0 0 .tip .tip)
private def heavy_doubleRight : Map (Fin 7) Nat := (.bin 4 5 5 (.bin 2 4 4 (.bin 1 3 3 .tip .tip) .tip) (.bin 1 6 6 .tip .tip))
private theorem heavy_doublePremises :
    Flapjack.FiniteMap.Comparison.goodCmp cmp ∧ keyOrdered cmp 1 heavy_doubleRight .lt ∧
    keyOrdered cmp 1 heavy_doubleLeft .gt ∧ almostBalancedR (size heavy_doubleLeft) (size heavy_doubleRight) ∧
    invariant cmp heavy_doubleLeft ∧ invariant cmp heavy_doubleRight := by
  refine ⟨good, ?_⟩
  simp [heavy_doubleLeft, heavy_doubleRight, keyOrdered, size, almostBalancedR, invariant, structureSize, balanced, delta, cmp]
  all_goals decide
private theorem heavy_doubleFull : invariant cmp (balanceR 1 50 heavy_doubleLeft heavy_doubleRight) ∧
    toFmap cmp (balanceR 1 50 heavy_doubleLeft heavy_doubleRight) =
    ((toFmap cmp heavy_doubleLeft).union (toFmap cmp heavy_doubleRight)).updateEq (keySet cmp 1, 50) :=
  balanceRThm 1 50 heavy_doubleLeft heavy_doubleRight cmp heavy_doublePremises
example : invariant cmp (balanceR 1 50 heavy_doubleLeft heavy_doubleRight) := heavy_doubleFull.1
example : toFmap cmp (balanceR 1 50 heavy_doubleLeft heavy_doubleRight) =
    ((toFmap cmp heavy_doubleLeft).union (toFmap cmp heavy_doubleRight)).updateEq (keySet cmp 1, 50) := heavy_doubleFull.2
example : (toFmap cmp (balanceR 1 50 heavy_doubleLeft heavy_doubleRight)).lookup (keySet cmp 1) = some 50 := by
  calc
    _ = lookup cmp 1 (balanceR 1 50 heavy_doubleLeft heavy_doubleRight) :=
      (lookupThm cmp 1 _ ⟨good, heavy_doubleFull.1⟩).symm
    _ = some 50 := rfl
end
end Flapjack.Test.BalancedMapBalanceRCorrectParity
