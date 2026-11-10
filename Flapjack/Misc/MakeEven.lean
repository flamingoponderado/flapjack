module

public import Flapjack.HolRef
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Alignment of natural numbers to the next even number. -/
namespace Flapjack

/-- Return the input when it is even, and its successor otherwise. -/
@[hol "cakeml/misc/miscScript.sml" "make_even_def"]
def makeEven (n : Nat) : Nat :=
  if n % 2 = 0 then n else n + 1

/-- The aligned result is even. -/
@[hol "cakeml/misc/miscScript.sml" "EVEN_make_even"]
theorem even_makeEven (n : Nat) : makeEven n % 2 = 0 := by
  unfold makeEven
  split <;> omega

end Flapjack
