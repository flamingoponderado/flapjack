import Flapjack.Misc.BalancedMap.RotationCorrect.SingleL
import Flapjack.Misc.BalancedMap.RotationCorrect.DoubleL

namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison
noncomputable section
local instance rotateLSetDecidableEq {κ : Type} : DecidableEq (Set κ) :=
  Classical.typeDecidableEq _

/-- Entire original left-rotation assembly. Heaviness excludes Tip, and the
literal strict ratio guard selects one of the complete constructor proofs.
No new constructor, post-state invariant or map equality is a premise. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "rotateL_thm"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem rotateLThm {κ ν : Type} (key : κ) (value : ν) (left right : Map κ ν)
    (cmp : κ → κ → Ordering)
    (h : goodCmp cmp ∧ keyOrdered cmp key right .lt ∧ keyOrdered cmp key left .gt ∧
      ¬ (size left + size right ≤ 1) ∧ size right > delta * size left ∧
      almostBalancedR (size left) (size right) ∧ invariant cmp left ∧ invariant cmp right) :
    invariant cmp (rotateL key value left right) ∧
    toFmap cmp (rotateL key value left right) =
      ((toFmap cmp left).union (toFmap cmp right)).updateEq (keySet cmp key, value) := by
  obtain ⟨hgood, hrightOrder, hleftOrder, hlarge, hheavy, halmost, hleftInv, hrightInv⟩ := h
  cases right with
  | tip =>
    change 0 > delta * size left at hheavy
    omega
  | bin n root rootValue middle last =>
    change ¬ (size left + n ≤ 1) at hlarge
    change n > delta * size left at hheavy
    change almostBalancedR (size left) n at halmost
    by_cases hratio : size middle < ratio * size last
    · simp only [rotateL, hratio]
      exact singleLThm key value left cmp n root rootValue middle last
        ⟨hgood, hrightOrder, hleftOrder, halmost,
          by simpa [Nat.add_comm] using hlarge, hheavy, hratio, hrightInv, hleftInv⟩
    · simp only [rotateL, hratio]
      exact doubleLThm key value left cmp n root rootValue middle last
        ⟨hgood, hrightOrder, hleftOrder, halmost,
          by simpa [Nat.add_comm] using hlarge, hheavy, hratio, hrightInv, hleftInv⟩

end
end Flapjack.Misc.BalancedMap
