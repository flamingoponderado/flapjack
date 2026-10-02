import Flapjack.Misc.BalancedMap.InsertCorrect
namespace Flapjack.Test.BalancedMapInsertCorrectParity
open Flapjack.Misc.BalancedMap
private def cmp (x y : Fin 7) : Ordering := compare x.val y.val
private theorem good : Flapjack.FiniteMap.Comparison.goodCmp cmp := by
  unfold Flapjack.FiniteMap.Comparison.goodCmp cmp
  decide
private def empty : Map (Fin 7) Nat := .tip
private def one : Map (Fin 7) Nat := .bin 1 3 30 .tip .tip
private theorem emptyInv : invariant cmp empty := by simp [empty, invariant]
private theorem oneInv : invariant cmp one := by
  simp [one, invariant, structureSize, keyOrdered, balanced, size, delta]
example : invariant cmp (insert cmp 3 31 empty) ∧
    toFmap cmp (insert cmp 3 31 empty) = (toFmap cmp empty).updateEq (keySet cmp 3, 31) :=
  insertThm cmp 3 31 empty ⟨good, emptyInv⟩
example : invariant cmp (insert cmp 1 11 one) ∧
    toFmap cmp (insert cmp 1 11 one) = (toFmap cmp one).updateEq (keySet cmp 1, 11) :=
  insertThm cmp 1 11 one ⟨good, oneInv⟩
example : invariant cmp (insert cmp 3 31 one) ∧
    toFmap cmp (insert cmp 3 31 one) = (toFmap cmp one).updateEq (keySet cmp 3, 31) :=
  insertThm cmp 3 31 one ⟨good, oneInv⟩
example : invariant cmp (insert cmp 5 51 one) ∧
    toFmap cmp (insert cmp 5 51 one) = (toFmap cmp one).updateEq (keySet cmp 5, 51) :=
  insertThm cmp 5 51 one ⟨good, oneInv⟩
private def equivalentCmp (_ _ : Fin 7) : Ordering := .eq
private theorem equivalentGood : Flapjack.FiniteMap.Comparison.goodCmp equivalentCmp := by
  unfold Flapjack.FiniteMap.Comparison.goodCmp equivalentCmp
  simp
private theorem equivalentInv : invariant equivalentCmp one := by
  simp [one, invariant, structureSize, keyOrdered, balanced, size, delta]
example : invariant equivalentCmp (insert equivalentCmp 2 99 one) ∧
    toFmap equivalentCmp (insert equivalentCmp 2 99 one) =
      (toFmap equivalentCmp one).updateEq (keySet equivalentCmp 2, 99) :=
  insertThm equivalentCmp 2 99 one ⟨equivalentGood, equivalentInv⟩
-- Comparator equality replaces the stored key even when the keys differ.
example : insert equivalentCmp 2 99 one = .bin 1 2 99 .tip .tip := by
  simp [Flapjack.Misc.BalancedMap.insert, equivalentCmp, one]

private def rotateRight : Map (Fin 7) Nat := .bin 2 3 30 (.bin 1 1 10 .tip .tip) .tip
private theorem rotateRightInv : invariant cmp rotateRight := by
  simp [rotateRight, invariant, structureSize, keyOrdered, balanced, size, delta, cmp]
  all_goals decide
example : invariant cmp (insert cmp 0 1 rotateRight) ∧
    toFmap cmp (insert cmp 0 1 rotateRight) =
      (toFmap cmp rotateRight).updateEq (keySet cmp 0, 1) :=
  insertThm cmp 0 1 rotateRight ⟨good, rotateRightInv⟩
private def rotateLeft : Map (Fin 7) Nat := .bin 2 3 30 .tip (.bin 1 5 50 .tip .tip)
private theorem rotateLeftInv : invariant cmp rotateLeft := by
  simp [rotateLeft, invariant, structureSize, keyOrdered, balanced, size, delta, cmp]
  all_goals decide
example : invariant cmp (insert cmp 6 61 rotateLeft) ∧
    toFmap cmp (insert cmp 6 61 rotateLeft) =
      (toFmap cmp rotateLeft).updateEq (keySet cmp 6, 61) :=
  insertThm cmp 6 61 rotateLeft ⟨good, rotateLeftInv⟩

-- Exact tree and lookup observations from the original HOL capture.
example : insert cmp 3 31 empty = .bin 1 3 31 .tip .tip := by decide
example : Flapjack.Misc.BalancedMap.lookup cmp 3 (insert cmp 3 31 empty) = some 31 := by decide
example : insert cmp 1 11 one = .bin 2 3 30 (.bin 1 1 11 .tip .tip) .tip := by decide
example : Flapjack.Misc.BalancedMap.lookup cmp 1 (insert cmp 1 11 one) = some 11 := by decide
example : insert cmp 3 31 one = .bin 1 3 31 .tip .tip := by decide
example : Flapjack.Misc.BalancedMap.lookup cmp 3 (insert cmp 3 31 one) = some 31 := by decide
example : insert cmp 5 51 one = .bin 2 3 30 .tip (.bin 1 5 51 .tip .tip) := by decide
example : Flapjack.Misc.BalancedMap.lookup cmp 5 (insert cmp 5 51 one) = some 51 := by decide
example : insert cmp 0 1 rotateRight = .bin 3 1 10 (.bin 1 0 1 .tip .tip) (.bin 1 3 30 .tip .tip) := by decide
example : Flapjack.Misc.BalancedMap.lookup cmp 0 (insert cmp 0 1 rotateRight) = some 1 := by decide
example : insert cmp 6 61 rotateLeft = .bin 3 5 50 (.bin 1 3 30 .tip .tip) (.bin 1 6 61 .tip .tip) := by decide
example : Flapjack.Misc.BalancedMap.lookup cmp 6 (insert cmp 6 61 rotateLeft) = some 61 := by decide
example : insert equivalentCmp 2 99 one = .bin 1 2 99 .tip .tip := by decide
example : Flapjack.Misc.BalancedMap.lookup equivalentCmp 2 (insert equivalentCmp 2 99 one) = some 99 := by decide
end Flapjack.Test.BalancedMapInsertCorrectParity
