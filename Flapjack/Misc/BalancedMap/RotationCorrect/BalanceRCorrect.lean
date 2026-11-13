module

public import Flapjack.Misc.BalancedMap.RotationCorrect.BalanceR
public import Flapjack.Misc.BalancedMap.OrderTrans
public import Flapjack.Misc.BalancedMap.RotationCorrect.RotateL

@[expose] public section
namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison
noncomputable section
local instance balanceRCorrectSetDecidableEq {κ : Type} : DecidableEq (Set κ) := Classical.typeDecidableEq _

/-- Entire original right-balancing correctness for the actual balanceR:
all original hypotheses and both invariant/map preservation conclusions. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanceR_thm"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem balanceRThm {κ ν : Type} (key : κ) (value : ν) (left right : Map κ ν)
    (cmp : κ → κ → Ordering)
    (h : goodCmp cmp ∧ keyOrdered cmp key right .lt ∧ keyOrdered cmp key left .gt ∧
      almostBalancedR (size left) (size right) ∧ invariant cmp left ∧ invariant cmp right) :
    invariant cmp (balanceR key value left right) ∧
    toFmap cmp (balanceR key value left right) =
      ((toFmap cmp left).union (toFmap cmp right)).updateEq (keySet cmp key, value) := by
  obtain ⟨hgood, hro, hlo, halmost, hl, hr⟩ := h
  rw [balanceRBalR key value left right cmp ⟨hgood, hl, hr⟩]
  unfold balR
  by_cases hsmall : size left + size right ≤ 1
  · rw [ite_eq_left hsmall]
    exact binCorrect key value left right cmp hl hr hlo hro
      (balancedLem1 _ _ hsmall)
  · rw [ite_eq_right hsmall]
    by_cases hheavy : size right > delta * size left
    · rw [ite_eq_left hheavy]
      exact rotateLThm key value left right cmp ⟨hgood, hro, hlo, hsmall, hheavy, halmost, hl, hr⟩
    · rw [ite_eq_right hheavy]
      exact binCorrect key value left right cmp hl hr hlo hro
        (balancedLem5 _ _ ⟨hheavy, halmost⟩)
end
end Flapjack.Misc.BalancedMap
