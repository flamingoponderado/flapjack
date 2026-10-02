import Flapjack.Misc.BalancedMap.CardinalityCorrect
namespace Flapjack.Test.BalancedMapCardinalityCorrectParity
open Flapjack.Misc.BalancedMap
private def cmp (x y : Fin 7) : Ordering := compare x.val y.val
private theorem good : Flapjack.FiniteMap.Comparison.goodCmp cmp := by
  unfold Flapjack.FiniteMap.Comparison.goodCmp cmp
  decide
private def empty : Map (Fin 7) Nat := .tip
private theorem emptyInv : invariant cmp empty := by
  simp [empty, invariant]
example : (toFmap cmp empty).card = structureSize empty :=
  structureSizeToFmap cmp empty good emptyInv
example : size empty = (toFmap cmp empty).card :=
  sizeThm cmp empty good emptyInv
private def singleton : Map (Fin 7) Nat := .bin 1 3 30 .tip .tip
private theorem singletonInv : invariant cmp singleton := by
  simp [singleton, invariant, structureSize, keyOrdered, balanced, size, delta]
example : (toFmap cmp singleton).card = structureSize singleton :=
  structureSizeToFmap cmp singleton good singletonInv
example : size singleton = (toFmap cmp singleton).card :=
  sizeThm cmp singleton good singletonInv
private def left : Map (Fin 7) Nat := .bin 2 3 30 (.bin 1 1 10 .tip .tip) .tip
private theorem leftInv : invariant cmp left := by
  simp [left, invariant, structureSize, keyOrdered, balanced, size, delta, cmp]
  all_goals decide
example : (toFmap cmp left).card = structureSize left :=
  structureSizeToFmap cmp left good leftInv
example : size left = (toFmap cmp left).card :=
  sizeThm cmp left good leftInv
private def right : Map (Fin 7) Nat := .bin 2 3 30 .tip (.bin 1 5 50 .tip .tip)
private theorem rightInv : invariant cmp right := by
  simp [right, invariant, structureSize, keyOrdered, balanced, size, delta, cmp]
  all_goals decide
example : (toFmap cmp right).card = structureSize right :=
  structureSizeToFmap cmp right good rightInv
example : size right = (toFmap cmp right).card :=
  sizeThm cmp right good rightInv
private def both : Map (Fin 7) Nat := .bin 3 3 30 (.bin 1 1 10 .tip .tip) (.bin 1 5 50 .tip .tip)
private theorem bothInv : invariant cmp both := by
  simp [both, invariant, structureSize, keyOrdered, balanced, size, delta, cmp]
  all_goals decide
example : (toFmap cmp both).card = structureSize both :=
  structureSizeToFmap cmp both good bothInv
example : size both = (toFmap cmp both).card :=
  sizeThm cmp both good bothInv
private def equivalentCmp (_ _ : Fin 7) : Ordering := .eq
private theorem equivalentGood : Flapjack.FiniteMap.Comparison.goodCmp equivalentCmp := by
  unfold Flapjack.FiniteMap.Comparison.goodCmp equivalentCmp
  simp
example : (toFmap equivalentCmp singleton).card = 1 := by
  have h : invariant equivalentCmp singleton := by
    simp [singleton, invariant, structureSize, keyOrdered, balanced, size, delta]
  simpa [structureSize, singleton] using structureSizeToFmap equivalentCmp singleton equivalentGood h
example : size singleton = (toFmap equivalentCmp singleton).card := by
  apply sizeThm equivalentCmp singleton equivalentGood
  simp [singleton, invariant, structureSize, keyOrdered, balanced, size, delta]
end Flapjack.Test.BalancedMapCardinalityCorrectParity
