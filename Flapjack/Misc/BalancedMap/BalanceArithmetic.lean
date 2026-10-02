import Flapjack.Misc.BalancedMap.Invariants
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

namespace Flapjack.Misc.BalancedMap

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "almost_balancedL_def"]
def almostBalancedL (l r : Nat) : Prop :=
  if l + r ≤ 1 ∨ l ≤ delta * r then balanced l r
  else if r = 0 then l < 5
  else if r = 1 then l < 8
  else 2 * l < (2 * delta + 3) * r + 2

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "almost_balancedR_def"]
def almostBalancedR (l r : Nat) : Prop :=
  if l + r ≤ 1 ∨ r ≤ delta * l then balanced l r
  else if l = 0 then r < 5
  else if l = 1 then r < 8
  else 2 * r < (2 * delta + 3) * l + 2

/-- Flapjack proof normalization of the literal min/max predicate. No separate
HOL original; it adds no hypotheses to the tagged rotation laws. -/
private theorem balancedLinear (l r : Nat) :
    balanced l r ↔ l + r ≤ 1 ∨ (l ≤ 3 * r ∧ r ≤ 3 * l) := by
  unfold balanced delta
  by_cases h : l ≤ r <;> simp [Nat.min_def, Nat.max_def, h] <;> omega

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanced_lem1"]
theorem balancedLem1 (l r : Nat) (h : l + r ≤ 1) : balanced l r := Or.inl h

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanced_lem2"]
theorem balancedLem2 (l r : Nat)
    (h : ¬ (l > delta * r) ∧ almostBalancedL l r ∧ ¬ (l + r ≤ 1)) :
    balanced l r := by
  simp only [almostBalancedL, balancedLinear, delta] at *
  split_ifs at h <;> omega

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanced_lem3"]
theorem balancedLem3 (b b0 r : Nat)
    (h : almostBalancedL (b + b0 + 1) r ∧ b + b0 + 1 > delta * r ∧
      b0 < ratio * b ∧ balanced b b0) :
    balanced b (b0 + r + 1) ∧ balanced b0 r := by
  simp only [almostBalancedL, balancedLinear, delta, ratio] at *
  split_ifs at h <;> omega

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanced_lem4"]
theorem balancedLem4 (b b' b0' r : Nat)
    (h : almostBalancedL (b + b' + b0' + 2) r ∧
      b + b' + b0' + 2 > delta * r ∧ ¬ (b' + b0' + 1 < ratio * b) ∧
      balanced b (b' + b0' + 1) ∧ balanced b' b0') :
    balanced (b + b' + 1) (b0' + r + 1) ∧ balanced b b' ∧ balanced b0' r := by
  simp only [almostBalancedL, balancedLinear, delta, ratio] at *
  split_ifs at h <;> omega

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanced_lem5"]
theorem balancedLem5 (l r : Nat)
    (h : ¬ (r > delta * l) ∧ almostBalancedR l r) : balanced l r := by
  simp only [almostBalancedR, balancedLinear, delta] at *
  split_ifs at h <;> omega

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanced_lem6"]
theorem balancedLem6 (b b0 l : Nat)
    (h : almostBalancedR l (b + b0 + 1) ∧ b + b0 + 1 > delta * l ∧
      b < ratio * b0 ∧ balanced b b0) :
    balanced (b + l + 1) b0 ∧ balanced l b := by
  simp only [almostBalancedR, balancedLinear, delta, ratio] at *
  split_ifs at h <;> omega

/-- HOL's first binder `b` is syntactically unused and has an independent
arbitrary type; retain it rather than narrowing it to Nat. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanced_lem7"]
theorem balancedLem7 {α : Type} (_b : α) (b0 b0' l b' : Nat)
    (h : almostBalancedR l (b' + b0 + b0' + 2) ∧
      b' + b0 + b0' + 2 > delta * l ∧ ¬ (b' + b0' + 1 < ratio * b0) ∧
      balanced (b' + b0' + 1) b0 ∧ balanced b' b0') :
    balanced (b' + l + 1) (b0 + b0' + 1) ∧ balanced l b' ∧ balanced b0' b0 := by
  simp only [almostBalancedR, balancedLinear, delta, ratio] at *
  split_ifs at h <;> omega

end Flapjack.Misc.BalancedMap
