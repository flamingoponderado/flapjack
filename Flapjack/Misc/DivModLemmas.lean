module

public import Flapjack.HolRef

@[expose] public section

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

/-- Full original `MOD_2EXP_0_EVEN`: a number divisible by `2 ** x` with
positive `x` is even. HOL's `MOD_2EXP x y` is `y MOD 2 ** x` and `EVEN y` is
the `y % 2 = 0` rendering. -/
@[hol "cakeml/misc/miscScript.sml" "MOD_2EXP_0_EVEN"]
theorem modTwoPowZeroEven (x y : Nat) (h : 0 < x ∧ y % 2 ^ x = 0) :
    y % 2 = 0 := by
  obtain ⟨hx, h⟩ := h
  have hdvd : 2 ^ x ∣ y := Nat.dvd_of_mod_eq_zero h
  have h2 : 2 ∣ 2 ^ x := by simpa using Nat.pow_dvd_pow 2 hx
  obtain ⟨c, hc⟩ := hdvd
  obtain ⟨d, hd⟩ := h2
  exact Nat.mod_eq_zero_of_dvd ⟨d * c, by rw [hc, hd, Nat.mul_assoc]⟩

end Flapjack.Misc.DivModLemmas
