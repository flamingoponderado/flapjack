module

public import Flapjack.Misc.BalancedMap.RotationCorrect.BalanceL
public import Flapjack.Misc.BalancedMap.OrderTrans
public import Flapjack.Misc.BalancedMap.RotationCorrect.RotateR

@[expose] public section
namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison
noncomputable section
local instance balanceLCorrectSetDecidableEq {κ : Type} : DecidableEq (Set κ) := Classical.typeDecidableEq _

/-- Entire original left-balancing correctness for the actual balanceL:
all original hypotheses and both invariant/map preservation conclusions. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanceL_thm"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem balanceLThm {κ ν : Type} (key : κ) (value : ν) (left right : Map κ ν)
    (cmp : κ → κ → Ordering)
    (h : goodCmp cmp ∧ keyOrdered cmp key left .gt ∧ keyOrdered cmp key right .lt ∧
      almostBalancedL (size left) (size right) ∧ invariant cmp left ∧ invariant cmp right) :
    invariant cmp (balanceL key value left right) ∧
    toFmap cmp (balanceL key value left right) =
      ((toFmap cmp left).union (toFmap cmp right)).updateEq (keySet cmp key, value) := by
  obtain ⟨hgood, hlo, hro, halmost, hl, hr⟩ := h
  rw [balanceLBalL key value left right cmp ⟨hgood, hl, hr⟩]
  unfold balL
  by_cases hsmall : size left + size right ≤ 1
  · rw [if_pos hsmall]
    exact binCorrect key value left right cmp hl hr hlo hro
      (balancedLem1 _ _ hsmall)
  · rw [if_neg hsmall]
    by_cases hheavy : size left > delta * size right
    · rw [if_pos hheavy]
      exact rotateRThm key value left right cmp ⟨hgood, hlo, hro, hsmall, hheavy, halmost, hl, hr⟩
    · rw [if_neg hheavy]
      exact binCorrect key value left right cmp hl hr hlo hro
        (balancedLem2 _ _ ⟨hheavy, halmost, hsmall⟩)
end
end Flapjack.Misc.BalancedMap
