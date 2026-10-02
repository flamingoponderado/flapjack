import Flapjack.Misc.BalancedMap.RotationCorrect.SingleR
import Flapjack.Misc.BalancedMap.RotationCorrect.DoubleR

namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison
noncomputable section
local instance rotateRSetDecidableEq {κ : Type} : DecidableEq (Set κ) :=
  Classical.typeDecidableEq _

/-- Entire original right-rotation assembly. Heaviness excludes Tip, and the
literal strict ratio guard selects one of the complete constructor proofs.
No new constructor, post-state invariant or map equality is a premise. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "rotateR_thm"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem rotateRThm {κ ν : Type} (key : κ) (value : ν) (left right : Map κ ν)
    (cmp : κ → κ → Ordering)
    (h : goodCmp cmp ∧ keyOrdered cmp key left .gt ∧ keyOrdered cmp key right .lt ∧
      ¬ (size left + size right ≤ 1) ∧ size left > delta * size right ∧
      almostBalancedL (size left) (size right) ∧ invariant cmp left ∧ invariant cmp right) :
    invariant cmp (rotateR key value left right) ∧
    toFmap cmp (rotateR key value left right) =
      ((toFmap cmp left).union (toFmap cmp right)).updateEq (keySet cmp key, value) := by
  obtain ⟨hgood, hleftOrder, hrightOrder, hlarge, hheavy, halmost, hleftInv, hrightInv⟩ := h
  cases left with
  | tip =>
    change 0 > delta * size right at hheavy
    omega
  | bin n root rootValue first middle =>
    change ¬ (n + size right ≤ 1) at hlarge
    change n > delta * size right at hheavy
    change almostBalancedL n (size right) at halmost
    by_cases hratio : size middle < ratio * size first
    · simp only [rotateR, hratio]
      exact singleRThm key value right cmp n root rootValue first middle
        ⟨hgood, hleftOrder, hrightOrder, halmost,
          by simpa [Nat.add_comm] using hlarge, hheavy, hratio, hleftInv, hrightInv⟩
    · simp only [rotateR, hratio]
      exact doubleRThm key value right cmp n root rootValue first middle
        ⟨hgood, hleftOrder, hrightOrder, halmost,
          by simpa [Nat.add_comm] using hlarge, hheavy, hratio, hleftInv, hrightInv⟩

end
end Flapjack.Misc.BalancedMap
