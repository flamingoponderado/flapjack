import Flapjack.Misc.Logroot

/-!
# HOL `bit`: `LOG2`

Counterpart of the pinned `hol4/src/num/extra_theories/bitScript.sml` for `LOG2`. `LOG2 0`
inherits the unconstrained value of the specified `LOG`; on positive arguments `LOG2` agrees
with Lean's `Nat.log2` by `LOG_UNIQUE`.
-/

namespace Flapjack

/-- Exact HOL `LOG2_def` (`bitScript.sml:54-55`): `LOG2 = LOG 2`. -/
@[hol "HOL/src/num/extra_theories/bitScript.sml" "LOG2_def"]
noncomputable def holLOG2 : Nat → Nat := holLOG 2

/-- On positive arguments HOL `LOG2` is Lean's `Nat.log2` (Flapjack infrastructure, from
`LOG_UNIQUE`); at `0` nothing is determined, as in HOL. -/
theorem holLOG2_eq_log2 {n : Nat} (hn : 0 < n) : holLOG2 n = Nat.log2 n :=
  holLOG_UNIQUE 2 n (Nat.log2 n) ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

end Flapjack
