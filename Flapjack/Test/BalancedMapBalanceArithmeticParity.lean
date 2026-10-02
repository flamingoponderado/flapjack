import Flapjack.Misc.BalancedMap.BalanceArithmetic

namespace Flapjack.Test.BalancedMapBalanceArithmeticParity
open Flapjack.Misc.BalancedMap

example : almostBalancedL 0 0 := by simp [almostBalancedL, balanced, delta]
example : almostBalancedL 4 0 := by simp [almostBalancedL, delta]
example : ¬ almostBalancedL 5 0 := by simp [almostBalancedL, delta]
example : almostBalancedL 7 1 := by simp [almostBalancedL, delta]
example : ¬ almostBalancedL 8 1 := by simp [almostBalancedL, delta]
example : almostBalancedL 9 2 := by simp [almostBalancedL, delta]
example : ¬ almostBalancedL 10 2 := by simp [almostBalancedL, delta]
example : almostBalancedR 0 0 := by simp [almostBalancedR, balanced, delta]
example : almostBalancedR 0 4 := by simp [almostBalancedR, delta]
example : ¬ almostBalancedR 0 5 := by simp [almostBalancedR, delta]
example : almostBalancedR 1 7 := by simp [almostBalancedR, delta]
example : ¬ almostBalancedR 1 8 := by simp [almostBalancedR, delta]
example : almostBalancedR 2 9 := by simp [almostBalancedR, delta]
example : ¬ almostBalancedR 2 10 := by simp [almostBalancedR, delta]

-- Original full statements remain usable with arbitrary sizes, including
-- lemma7's unconstrained, syntactically unused independent binder.
example (l r : Nat) (h : l + r ≤ 1) : balanced l r := balancedLem1 l r h
example (b b0 r : Nat)
    (h : almostBalancedL (b + b0 + 1) r ∧ b + b0 + 1 > delta * r ∧
      b0 < ratio * b ∧ balanced b b0) :
    balanced b (b0 + r + 1) ∧ balanced b0 r := balancedLem3 b b0 r h
example {α : Type} (unused : α) (b0 b0' l b' : Nat)
    (h : almostBalancedR l (b' + b0 + b0' + 2) ∧
      b' + b0 + b0' + 2 > delta * l ∧ ¬ (b' + b0' + 1 < ratio * b0) ∧
      balanced (b' + b0' + 1) b0 ∧ balanced b' b0') :
    balanced (b' + l + 1) (b0 + b0' + 1) ∧ balanced l b' ∧ balanced b0' b0 :=
  balancedLem7 unused b0 b0' l b' h

end Flapjack.Test.BalancedMapBalanceArithmeticParity
