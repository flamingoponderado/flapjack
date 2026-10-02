import Flapjack.Misc.Bit

namespace Flapjack.Test.LogrootParity
open Flapjack

/-! Replay of `scripts/hol-probes/logroot_log_spec_probe.out`: the original HOL statements of
`LOG_exists`, `LOG`, `LOG_UNIQUE` and `LOG2_def` against the Lean declarations, and the
probe's `LOG2` values on positive arguments, which HOL proves from `LOG_UNIQUE` (`LOG2` is
`[nocompute]`) and are proved here the same way. No value of `LOG2 0` is derivable on either
side. -/

-- lg_log_exists=∃f. ∀a n. 1 < a ∧ 0 < n ⇒ a ** f a n ≤ n ∧ n < a ** SUC (f a n)
example : ∃ f : Nat → Nat → Nat, ∀ a n : Nat, 1 < a ∧ 0 < n → a ^ f a n ≤ n ∧ n < a ^ (f a n + 1) :=
  holLOGExists
-- lg_log_spec=∀a n. 1 < a ∧ 0 < n ⇒ a ** LOG a n ≤ n ∧ n < a ** SUC (LOG a n)
example : ∀ a n : Nat, 1 < a ∧ 0 < n → a ^ holLOG a n ≤ n ∧ n < a ^ (holLOG a n + 1) :=
  holLOG_spec
-- lg_log_unique=∀a n p. a ** p ≤ n ∧ n < a ** SUC p ⇒ LOG a n = p
example : ∀ a n p : Nat, a ^ p ≤ n ∧ n < a ^ (p + 1) → holLOG a n = p := holLOG_UNIQUE
-- lg_log2_def=LOG2 = LOG 2
example : holLOG2 = holLOG 2 := rfl
-- lg_log2_8=LOG2 8 = 3
example : holLOG2 8 = 3 := holLOG_UNIQUE 2 8 3 ⟨by decide, by decide⟩
-- lg_log2_1=LOG2 1 = 0
example : holLOG2 1 = 0 := holLOG_UNIQUE 2 1 0 ⟨by decide, by decide⟩
-- lg_log2_9=LOG2 9 = 3
example : holLOG2 9 = 3 := holLOG_UNIQUE 2 9 3 ⟨by decide, by decide⟩
-- lg_log2_64=LOG2 64 = 6
example : holLOG2 64 = 6 := holLOG_UNIQUE 2 64 6 ⟨by decide, by decide⟩

end Flapjack.Test.LogrootParity
