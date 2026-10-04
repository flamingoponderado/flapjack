import Flapjack.HolRef

/-! `miscScript.sml` natural-number `DIV`/`MOD` lemmas cited by the
Pancake-to-target proof. HOL `num` is `Nat` (truncated subtraction, `DIV`/`MOD`
by zero as in Lean). -/
namespace Flapjack.Misc.DivModLemmas

/-- Full original `MOD_SUB_LEMMA`:
`n MOD k = 0 /\ m MOD k = 0 /\ 0 < k ==> (n - m) MOD k = 0`. -/
@[hol "cakeml/misc/miscScript.sml" "MOD_SUB_LEMMA"]
theorem modSubLemma {n m k : Nat} (h : n % k = 0 ∧ m % k = 0 ∧ 0 < k) :
    (n - m) % k = 0 :=
  Nat.mod_eq_zero_of_dvd
    (Nat.dvd_sub (Nat.dvd_of_mod_eq_zero h.1) (Nat.dvd_of_mod_eq_zero h.2.1))

/-- Full original `IMP_MULT_DIV_LESS`: `m <> 0 /\ d < k ==> m * (d DIV m) < k`. -/
@[hol "cakeml/misc/miscScript.sml" "IMP_MULT_DIV_LESS"]
theorem impMultDivLess {m d k : Nat} (h : m ≠ 0 ∧ d < k) : m * (d / m) < k :=
  Nat.lt_of_le_of_lt (Nat.mul_div_le d m) h.2

/-- Full original `DIV_LESS_DIV`:
`n MOD k = 0 /\ m MOD k = 0 /\ n < m /\ 0 < k ==> n DIV k < m DIV k`. -/
@[hol "cakeml/misc/miscScript.sml" "DIV_LESS_DIV"]
theorem divLessDiv {n m k : Nat} (h : n % k = 0 ∧ m % k = 0 ∧ n < m ∧ 0 < k) :
    n / k < m / k := by
  obtain ⟨hn, hm, hlt, hk⟩ := h
  have en : k * (n / k) = n := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hn)
  have em : k * (m / k) = m := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)
  rw [← en, ← em] at hlt
  exact Nat.lt_of_mul_lt_mul_left hlt

end Flapjack.Misc.DivModLemmas
