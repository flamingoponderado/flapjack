import Flapjack.HolRef
import Lean.Elab.Tactic.Omega

/-! Counterpart of pinned HOL numposrepScript numeric digit conversion. -/
namespace Flapjack

/-- Least-significant digit first, including literal HOL base-zero/base-one behavior. -/
@[hol "HOL/src/list/src/numposrepScript.sml" "n2l_def"]
def holN2l (b n : Nat) : List Nat :=
  if n < b ∨ b < 2 then [n % b]
  else n % b :: holN2l b (n / b)
termination_by n
decreasing_by
  have _h : ¬ (n < b ∨ b < 2) := by assumption
  exact Nat.div_lt_self (by omega) (by omega)

end Flapjack
