module

public import Flapjack.Misc.Logroot

@[expose] public section

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
`LOG_UNIQUE`); at `0` the specification does not constrain it, as in HOL. -/
theorem holLOG2_eq_log2 {n : Nat} (hn : 0 < n) : holLOG2 n = Nat.log2 n :=
  holLOG_UNIQUE 2 n (Nat.log2 n) ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

/-- Original `LOG2_TIMES2`: for a positive argument, multiplying by two adds one
to the base-2 logarithm. -/
@[hol "cakeml/misc/miscScript.sml" "LOG2_TIMES2"]
theorem holLOG2_two_mul (n : Nat) (h : 0 < n) :
    holLOG2 (2 * n) = holLOG2 n + 1 := by
  rw [holLOG2_eq_log2 (by omega), holLOG2_eq_log2 h, Nat.log2_two_mul (by omega)]

/-- Original `LOG2_TIMES2_1`: an odd argument just above a doubled one has the
same base-2 logarithm. -/
@[hol "cakeml/misc/miscScript.sml" "LOG2_TIMES2_1"]
theorem holLOG2_two_mul_add_one (n : Nat) (h : 0 < n) :
    holLOG2 (2 * n + 1) = holLOG2 (2 * n) := by
  rw [holLOG2_eq_log2 (by omega), holLOG2_eq_log2 (by omega)]
  have hne : 2 * n ≠ 0 := by omega
  have hle : 2 ^ Nat.log2 (2 * n) ≤ 2 * n + 1 := by
    have := (Nat.le_log2 hne).mp (Nat.le_refl _)
    omega
  have hlt : 2 * n + 1 < 2 ^ (Nat.log2 (2 * n) + 1) := by
    have hlt' := (Nat.log2_lt hne).mp (Nat.lt_succ_self (Nat.log2 (2 * n)))
    rw [Nat.pow_succ]
    omega
  exact (Nat.log2_eq_iff (by omega)).mpr ⟨hle, hlt⟩

end Flapjack
