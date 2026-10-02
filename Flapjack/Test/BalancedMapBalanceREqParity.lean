import Flapjack.Misc.BalancedMap.RotationCorrect.BalanceR
namespace Flapjack.Test.BalancedMapBalanceREqParity
open Flapjack.Misc.BalancedMap
private def cmp (x y : Fin 7) : Ordering := compare x.val y.val
private theorem good : Flapjack.FiniteMap.Comparison.goodCmp cmp := by
  unfold Flapjack.FiniteMap.Comparison.goodCmp cmp
  decide
private def emptyLeft : Map (Fin 7) Nat := .tip
private def emptyRight : Map (Fin 7) Nat := .tip
private theorem emptyInv : invariant cmp emptyLeft ∧ invariant cmp emptyRight := by
  simp [emptyLeft, emptyRight, invariant]
example : balanceR 1 50 emptyLeft emptyRight = balR 1 50 emptyLeft emptyRight :=
  balanceRBalR 1 50 emptyLeft emptyRight cmp ⟨good, emptyInv.1, emptyInv.2⟩
private def singletonLeft : Map (Fin 7) Nat := .tip
private def singletonRight : Map (Fin 7) Nat := (.bin 1 6 6 .tip .tip)
private theorem singletonInv : invariant cmp singletonLeft ∧ invariant cmp singletonRight := by
  simp [singletonLeft, singletonRight, invariant, structureSize, keyOrdered, balanced, size, delta]
example : balanceR 1 50 singletonLeft singletonRight = balR 1 50 singletonLeft singletonRight :=
  balanceRBalR 1 50 singletonLeft singletonRight cmp ⟨good, singletonInv.1, singletonInv.2⟩
private def lr_onlyLeft : Map (Fin 7) Nat := .tip
private def lr_onlyRight : Map (Fin 7) Nat := (.bin 2 6 6 (.bin 1 5 5 .tip .tip) .tip)
private theorem lr_onlyInv : invariant cmp lr_onlyLeft ∧ invariant cmp lr_onlyRight := by
  simp [lr_onlyLeft, lr_onlyRight, invariant, structureSize, keyOrdered, balanced, size, delta, cmp]
  all_goals decide
example : balanceR 1 50 lr_onlyLeft lr_onlyRight = balR 1 50 lr_onlyLeft lr_onlyRight :=
  balanceRBalR 1 50 lr_onlyLeft lr_onlyRight cmp ⟨good, lr_onlyInv.1, lr_onlyInv.2⟩
private def ll_onlyLeft : Map (Fin 7) Nat := .tip
private def ll_onlyRight : Map (Fin 7) Nat := (.bin 2 5 5 .tip (.bin 1 6 6 .tip .tip))
private theorem ll_onlyInv : invariant cmp ll_onlyLeft ∧ invariant cmp ll_onlyRight := by
  simp [ll_onlyLeft, ll_onlyRight, invariant, structureSize, keyOrdered, balanced, size, delta, cmp]
  all_goals decide
example : balanceR 1 50 ll_onlyLeft ll_onlyRight = balR 1 50 ll_onlyLeft ll_onlyRight :=
  balanceRBalR 1 50 ll_onlyLeft ll_onlyRight cmp ⟨good, ll_onlyInv.1, ll_onlyInv.2⟩
private def single_tipLeft : Map (Fin 7) Nat := .tip
private def single_tipRight : Map (Fin 7) Nat := (.bin 3 5 5 (.bin 1 4 4 .tip .tip) (.bin 1 6 6 .tip .tip))
private theorem single_tipInv : invariant cmp single_tipLeft ∧ invariant cmp single_tipRight := by
  simp [single_tipLeft, single_tipRight, invariant, structureSize, keyOrdered, balanced, size, delta, cmp]
  all_goals decide
example : balanceR 1 50 single_tipLeft single_tipRight = balR 1 50 single_tipLeft single_tipRight :=
  balanceRBalR 1 50 single_tipLeft single_tipRight cmp ⟨good, single_tipInv.1, single_tipInv.2⟩
private def double_tipLeft : Map (Fin 7) Nat := .tip
private def double_tipRight : Map (Fin 7) Nat := (.bin 4 5 5 (.bin 2 4 4 (.bin 1 3 3 .tip .tip) .tip) (.bin 1 6 6 .tip .tip))
private theorem double_tipInv : invariant cmp double_tipLeft ∧ invariant cmp double_tipRight := by
  simp [double_tipLeft, double_tipRight, invariant, structureSize, keyOrdered, balanced, size, delta, cmp]
  all_goals decide
example : balanceR 1 50 double_tipLeft double_tipRight = balR 1 50 double_tipLeft double_tipRight :=
  balanceRBalR 1 50 double_tipLeft double_tipRight cmp ⟨good, double_tipInv.1, double_tipInv.2⟩
private def left_tipLeft : Map (Fin 7) Nat := (.bin 1 0 0 .tip .tip)
private def left_tipRight : Map (Fin 7) Nat := .tip
private theorem left_tipInv : invariant cmp left_tipLeft ∧ invariant cmp left_tipRight := by
  simp [left_tipLeft, left_tipRight, invariant, structureSize, keyOrdered, balanced, size, delta]
example : balanceR 1 50 left_tipLeft left_tipRight = balR 1 50 left_tipLeft left_tipRight :=
  balanceRBalR 1 50 left_tipLeft left_tipRight cmp ⟨good, left_tipInv.1, left_tipInv.2⟩
private def fallbackLeft : Map (Fin 7) Nat := (.bin 1 0 0 .tip .tip)
private def fallbackRight : Map (Fin 7) Nat := (.bin 2 5 5 .tip (.bin 1 6 6 .tip .tip))
private theorem fallbackInv : invariant cmp fallbackLeft ∧ invariant cmp fallbackRight := by
  simp [fallbackLeft, fallbackRight, invariant, structureSize, keyOrdered, balanced, size, delta, cmp]
  all_goals decide
example : balanceR 1 50 fallbackLeft fallbackRight = balR 1 50 fallbackLeft fallbackRight :=
  balanceRBalR 1 50 fallbackLeft fallbackRight cmp ⟨good, fallbackInv.1, fallbackInv.2⟩
private def heavy_singleLeft : Map (Fin 7) Nat := (.bin 1 0 0 .tip .tip)
private def heavy_singleRight : Map (Fin 7) Nat := (.bin 4 4 4 (.bin 1 3 3 .tip .tip) (.bin 2 5 5 .tip (.bin 1 6 6 .tip .tip)))
private theorem heavy_singleInv : invariant cmp heavy_singleLeft ∧ invariant cmp heavy_singleRight := by
  simp [heavy_singleLeft, heavy_singleRight, invariant, structureSize, keyOrdered, balanced, size, delta, cmp]
  all_goals decide
example : balanceR 1 50 heavy_singleLeft heavy_singleRight = balR 1 50 heavy_singleLeft heavy_singleRight :=
  balanceRBalR 1 50 heavy_singleLeft heavy_singleRight cmp ⟨good, heavy_singleInv.1, heavy_singleInv.2⟩
private def heavy_doubleLeft : Map (Fin 7) Nat := (.bin 1 0 0 .tip .tip)
private def heavy_doubleRight : Map (Fin 7) Nat := (.bin 4 5 5 (.bin 2 4 4 (.bin 1 3 3 .tip .tip) .tip) (.bin 1 6 6 .tip .tip))
private theorem heavy_doubleInv : invariant cmp heavy_doubleLeft ∧ invariant cmp heavy_doubleRight := by
  simp [heavy_doubleLeft, heavy_doubleRight, invariant, structureSize, keyOrdered, balanced, size, delta, cmp]
  all_goals decide
example : balanceR 1 50 heavy_doubleLeft heavy_doubleRight = balR 1 50 heavy_doubleLeft heavy_doubleRight :=
  balanceRBalR 1 50 heavy_doubleLeft heavy_doubleRight cmp ⟨good, heavy_doubleInv.1, heavy_doubleInv.2⟩
end Flapjack.Test.BalancedMapBalanceREqParity
