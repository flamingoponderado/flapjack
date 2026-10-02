import Flapjack.Misc.BalancedMap.BalanceArithmetic
namespace Flapjack.Misc.BalancedMap
/-- Arithmetic normalization infrastructure, not a separate HOL declaration. -/
private theorem balancedLinear (l r : Nat) :
    balanced l r ↔ l + r ≤ 1 ∨ (l ≤ 3 * r ∧ r ≤ 3 * l) := by
  unfold balanced delta
  by_cases h : l ≤ r <;> simp [Nat.min_def, Nat.max_def, h] <;> omega
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "almost_balancedL_thm"]
theorem almostBalancedLThm (l r : Nat) (h : balanced l r) :
    almostBalancedL l r ∧ almostBalancedL (l + 1) r ∧
    almostBalancedL l (r - 1) := by
  simp only [almostBalancedL, balancedLinear, delta] at *
  split_ifs <;> omega
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "almost_balancedR_thm"]
theorem almostBalancedRThm (l r : Nat) (h : balanced l r) :
    almostBalancedR l r ∧ almostBalancedR l (r + 1) ∧
    almostBalancedR (l - 1) r := by
  simp only [almostBalancedR, balancedLinear, delta] at *
  split_ifs <;> omega
end Flapjack.Misc.BalancedMap
