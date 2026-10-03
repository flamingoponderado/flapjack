import Flapjack.Misc.BinaryIeeeSqrt
import Flapjack.Misc.BinaryIeeeRoundFp64

/-!
# Computable binary64 square root, proved equal to the sqrt specification

For binary64 (bead `flapjack-h29l.6.3.2.2`), this module defines the
computable `holFp64SqrtRoundRte` and proves `holFloatRoundSqrt_rte_fp64`, a
kernel-checked theorem.  For every rational `r ≥ 0`, it states that the
rational-cut rendering `holFloatRoundSqrt roundTiesToEven toneg r` of HOL's
choice-based `float_round roundTiesToEven toneg (sqrt r)`
(`Flapjack.Misc.BinaryIeeeSqrt`) equals the computable function.
`holFp64Sqrt_rte` lifts this to `fp64_sqrt`.

The algorithm works in units of `2^-1074`, where the target is
`S = sqrt R` with `R = r * 2^2148`:
* `Nat.sqrt ⌊R⌋` brackets `S` between the patterns `fp64Bracket` and its
  successor (`fp64BracketSqrt`);
* the nearer pattern is chosen by comparing `R` with the squared bracket
  midpoint, and a tie goes to the even pattern (`fp64NearestSqrt_cases`).

The closeness and uniqueness lemmas (`fp64NearestSqrt_le_pos/neg`,
`fp64NearestSqrt_eq_pos/neg`) reduce to comparisons of `S` with midpoints.
Those are the rational criteria of the specification, through the cut-order
lemmas `holSqrtLe_Ge_lt`, `holSqrtLt_Ge` and `holSqrtLe_Gt`.  The real-number
meaning of those criteria is the external assumption recorded in
`docs/SOUNDNESS.md`.  HOL standard library, so untagged.
-/

namespace Flapjack

section Cut

variable {R : Rat}

theorem rat_sq_le_sq {a b : Rat} (ha : 0 ≤ a) (h : a ≤ b) : a * a ≤ b * b := by
  have hb : 0 ≤ b := by grind
  have h1 : a * a ≤ a * b := Rat.mul_le_mul_of_nonneg_left h ha
  have h2 : a * b ≤ b * b := Rat.mul_le_mul_of_nonneg_right h hb
  grind

theorem rat_sq_lt_sq {a b : Rat} (ha : 0 ≤ a) (h : a < b) : a * a < b * b := by
  have hb : 0 < b := by grind
  have h1 : a * a ≤ a * b := Rat.mul_le_mul_of_nonneg_left (by grind) ha
  have h2 : a * b < b * b := Rat.mul_lt_mul_of_pos_right h hb
  grind

theorem holSqrtLe_mono {m m' : Rat} (h : holSqrtLe R m) (hm : m ≤ m') : holSqrtLe R m' := by
  obtain ⟨h0, h1⟩ := h
  exact ⟨by grind, by have := rat_sq_le_sq h0 hm; grind⟩

theorem holSqrtGe_mono {m m' : Rat} (h : holSqrtGe R m) (hm : m' ≤ m) : holSqrtGe R m' := by
  rcases h with h | h
  · exact Or.inl (by grind)
  · by_cases h0 : m' ≤ 0
    · exact Or.inl h0
    · right; have := rat_sq_le_sq (show 0 ≤ m' by grind) hm; grind

theorem holSqrtLe_Ge_lt {m m' : Rat} (h1 : holSqrtLe R m) (h2 : holSqrtGe R m') (hm : m < m') :
    False := by
  obtain ⟨h0, hr⟩ := h1
  rcases h2 with h | h
  · grind
  · have := rat_sq_lt_sq h0 hm; grind

theorem holSqrtLt_Ge {m m' : Rat} (h1 : holSqrtLt R m) (h2 : holSqrtGe R m') (hm : m ≤ m') :
    False := by
  obtain ⟨h0, hr⟩ := h1
  rcases h2 with h | h
  · grind
  · have := rat_sq_le_sq (by grind) hm; grind

theorem holSqrtLe_Gt {m m' : Rat} (h1 : holSqrtLe R m) (h2 : holSqrtGt R m') (hm : m ≤ m') :
    False := by
  obtain ⟨h0, hr⟩ := h1
  rcases h2 with h | h
  · grind
  · have := rat_sq_le_sq h0 hm; grind

end Cut


/-- The pattern nearest to `S = sqrt R` (in units of `2^-1074`, `R ≥ 0`), ties
    to the even pattern: bracket `S` by `Nat.sqrt ⌊R⌋`, then compare `R` with
    the square of the bracket midpoint. -/
def fp64NearestSqrt (R : Rat) : Nat :=
  let p := fp64Bracket (Nat.sqrt R.floor.toNat)
  let lo : Rat := ((fp64N p : Nat) : Rat)
  let hi : Rat := ((fp64N (p + 1) : Nat) : Rat)
  let m := (lo + hi) / 2
  if R < m * m then p
  else if m * m < R then p + 1
  else if p % 2 = 0 then p else p + 1

section NearestSqrt

variable {R : Rat}

private theorem nat_cast_mul (a b : Nat) : ((a * b : Nat) : Rat) = (a : Rat) * (b : Rat) := by
  push_cast; rfl

/-- The bracket of `sqrt R`: `lo ≤ sqrt R < hi`. -/
theorem fp64BracketSqrt (hR : 0 ≤ R) :
    holSqrtGe R ((fp64N (fp64Bracket (Nat.sqrt R.floor.toNat)) : Nat) : Rat) ∧
      holSqrtLt R ((fp64N (fp64Bracket (Nat.sqrt R.floor.toNat) + 1) : Nat) : Rat) := by
  generalize hk : R.floor.toNat = k
  have ⟨hb1, hb2⟩ := fp64Bracket_spec (Nat.sqrt k)
  have hs1 := Nat.sqrt_le k
  have hs2 := Nat.lt_succ_sqrt k
  generalize Nat.sqrt k = n at *
  generalize fp64N (fp64Bracket n) = lo at *
  generalize fp64N (fp64Bracket n + 1) = hi at *
  have hfl : 0 ≤ R.floor := Rat.le_floor_iff.2 (by simpa using hR)
  have hkR : (k : Rat) ≤ R := by
    have h := congrArg (fun z : Int => (z : Rat)) (Int.toNat_of_nonneg hfl)
    rw [hk] at h
    have := Rat.floor_le R
    rw [← h] at this
    exact this
  have hRk : R < (k : Rat) + 1 := by
    have h := congrArg (fun z : Int => (z : Rat)) (Int.toNat_of_nonneg hfl)
    rw [hk] at h
    have := Rat.lt_floor_add_one R
    push_cast at this
    rw [← h] at this
    exact this
  have hlo : lo * lo ≤ k := Nat.le_trans (Nat.mul_le_mul hb1 hb1) hs1
  have hhi : k + 1 ≤ hi * hi := by
    have : n + 1 ≤ hi := hb2
    have := Nat.mul_le_mul this this
    simp only [Nat.succ_eq_add_one] at hs2
    omega
  have hlo' : ((lo * lo : Nat) : Rat) ≤ (k : Rat) := by exact_mod_cast hlo
  have hhi' : ((k + 1 : Nat) : Rat) ≤ ((hi * hi : Nat) : Rat) := by exact_mod_cast hhi
  rw [nat_cast_mul] at hlo' hhi'
  push_cast at hhi'
  have hhipos : (0 : Rat) < (hi : Rat) := by
    have : 0 < hi := by omega
    exact_mod_cast this
  exact ⟨Or.inr (by grind), ⟨hhipos, by grind⟩⟩

/-- The choice of `fp64NearestSqrt`.  The lower pattern is chosen when
    `sqrt R` is at most the midpoint, the upper one when it is at least the
    midpoint, and at a tie (both) the chosen pattern is even. -/
theorem fp64NearestSqrt_cases :
    (fp64NearestSqrt R = fp64Bracket (Nat.sqrt R.floor.toNat) ∧
        holSqrtLe R ((((fp64N (fp64Bracket (Nat.sqrt R.floor.toNat)) : Nat) : Rat) +
          ((fp64N (fp64Bracket (Nat.sqrt R.floor.toNat) + 1) : Nat) : Rat)) / 2) ∧
        (holSqrtGe R ((((fp64N (fp64Bracket (Nat.sqrt R.floor.toNat)) : Nat) : Rat) +
          ((fp64N (fp64Bracket (Nat.sqrt R.floor.toNat) + 1) : Nat) : Rat)) / 2) →
          fp64NearestSqrt R % 2 = 0)) ∨
      (fp64NearestSqrt R = fp64Bracket (Nat.sqrt R.floor.toNat) + 1 ∧
        holSqrtGe R ((((fp64N (fp64Bracket (Nat.sqrt R.floor.toNat)) : Nat) : Rat) +
          ((fp64N (fp64Bracket (Nat.sqrt R.floor.toNat) + 1) : Nat) : Rat)) / 2) ∧
        (holSqrtLe R ((((fp64N (fp64Bracket (Nat.sqrt R.floor.toNat)) : Nat) : Rat) +
          ((fp64N (fp64Bracket (Nat.sqrt R.floor.toNat) + 1) : Nat) : Rat)) / 2) →
          fp64NearestSqrt R % 2 = 0)) := by
  have hstrict := fp64N_strictMono (Nat.lt_succ_self (fp64Bracket (Nat.sqrt R.floor.toNat)))
  unfold fp64NearestSqrt
  simp only
  generalize fp64Bracket (Nat.sqrt R.floor.toNat) = p at *
  have h0 : (0 : Rat) ≤ ((fp64N p : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  have h1' : ((fp64N p : Nat) : Rat) < ((fp64N (p + 1) : Nat) : Rat) := by exact_mod_cast hstrict
  generalize ((fp64N p : Nat) : Rat) = lo at *
  generalize ((fp64N (p + 1) : Nat) : Rat) = hi at *
  have hm : 0 < (lo + hi) / 2 := by grind
  generalize (lo + hi) / 2 = m at *
  unfold holSqrtLe holSqrtGe
  by_cases c1 : R < m * m
  · rw [if_pos c1]
    left; exact ⟨rfl, ⟨by grind, by grind⟩, fun h => by exfalso; grind⟩
  · rw [if_neg c1]
    by_cases c2 : m * m < R
    · rw [if_pos c2]
      right; exact ⟨rfl, Or.inr (by grind), fun h => by exfalso; grind⟩
    · rw [if_neg c2]
      by_cases hp : p % 2 = 0
      · rw [if_pos hp]
        left; exact ⟨rfl, ⟨by grind, by grind⟩, fun _ => hp⟩
      · rw [if_neg hp]
        right; exact ⟨rfl, Or.inr (by grind), fun _ => by omega⟩

private theorem fp64N_cast_nonneg (q : Nat) : (0 : Rat) ≤ ((fp64N q : Nat) : Rat) := by
  exact_mod_cast Nat.zero_le _

private theorem fp64N_cast_le' {q r : Nat} (h : q ≤ r) :
    ((fp64N q : Nat) : Rat) ≤ ((fp64N r : Nat) : Rat) := by exact_mod_cast fp64N_mono h

private theorem fp64N_cast_lt' {q r : Nat} (h : q < r) :
    ((fp64N q : Nat) : Rat) < ((fp64N r : Nat) : Rat) := by exact_mod_cast fp64N_strictMono h

private theorem holSqrtLe_of_lt {q : Rat} (h : holSqrtLt R q) : holSqrtLe R q :=
  ⟨Rat.le_of_lt h.1, Rat.le_of_lt h.2⟩

private theorem fp64N_inj {q r : Nat} (h : ((fp64N q : Nat) : Rat) = ((fp64N r : Nat) : Rat)) :
    q = r := by
  rcases Nat.lt_trichotomy q r with hlt | heq | hgt
  · have := fp64N_cast_lt' hlt; exfalso; grind
  · exact heq
  · have := fp64N_cast_lt' hgt; exfalso; grind

/-- The nearest pattern is at least as close to `sqrt R` as every nonnegative
    value. -/
theorem fp64NearestSqrt_le_pos (hR : 0 ≤ R) (q : Nat) :
    holSqrtDistLe R ((fp64N (fp64NearestSqrt R) : Nat) : Rat) ((fp64N q : Nat) : Rat) := by
  have ⟨hlo, hhi⟩ := fp64BracketSqrt hR
  have hcase := fp64NearestSqrt_cases (R := R)
  generalize fp64NearestSqrt R = a at *
  generalize fp64Bracket (Nat.sqrt R.floor.toNat) = p at *
  have hlohi := fp64N_cast_lt' (Nat.lt_succ_self p)
  unfold holSqrtDistLe
  rcases hcase with ⟨ha, hle, _⟩ | ⟨ha, hge, _⟩
  · rw [ha]
    by_cases hq : q ≤ p
    · have := fp64N_cast_le' hq
      rcases Rat.le_iff_lt_or_eq.1 this with h | h
      · exact Or.inr (Or.inr ⟨h, holSqrtGe_mono hlo (by grind)⟩)
      · exact Or.inl h.symm
    · have := fp64N_cast_le' (show p + 1 ≤ q by omega)
      exact Or.inr (Or.inl ⟨by grind, holSqrtLe_mono hle (by grind)⟩)
  · rw [ha]
    by_cases hq : p + 1 ≤ q
    · have := fp64N_cast_le' hq
      rcases Rat.le_iff_lt_or_eq.1 this with h | h
      · exact Or.inr (Or.inl ⟨h, holSqrtLe_mono (holSqrtLe_of_lt hhi) (by grind)⟩)
      · exact Or.inl h
    · have := fp64N_cast_le' (show q ≤ p by omega)
      exact Or.inr (Or.inr ⟨by grind, holSqrtGe_mono hge (by grind)⟩)

/-- The nearest pattern is at least as close to `sqrt R` as every
    nonpositive value. -/
theorem fp64NearestSqrt_le_neg (hR : 0 ≤ R) (q : Nat) :
    holSqrtDistLe R ((fp64N (fp64NearestSqrt R) : Nat) : Rat) (-((fp64N q : Nat) : Rat)) := by
  have ⟨hlo, _⟩ := fp64BracketSqrt hR
  have hcase := fp64NearestSqrt_cases (R := R)
  generalize fp64NearestSqrt R = a at *
  generalize fp64Bracket (Nat.sqrt R.floor.toNat) = p at *
  have hlohi := fp64N_cast_lt' (Nat.lt_succ_self p)
  have h0 := fp64N_cast_nonneg p
  have hq0 := fp64N_cast_nonneg q
  unfold holSqrtDistLe
  rcases hcase with ⟨ha, _, _⟩ | ⟨ha, hge, _⟩
  · rw [ha]
    rcases Rat.le_iff_lt_or_eq.1 (show -((fp64N q : Nat) : Rat) ≤ ((fp64N p : Nat) : Rat) by grind)
      with h | h
    · exact Or.inr (Or.inr ⟨h, holSqrtGe_mono hlo (by grind)⟩)
    · exact Or.inl h.symm
  · rw [ha]
    exact Or.inr (Or.inr ⟨by grind, holSqrtGe_mono hge (by grind)⟩)

/-- A nonnegative value as close to `sqrt R` as the nearest pattern is the
    nearest pattern, or its odd partner at a tie. -/
theorem fp64NearestSqrt_eq_pos (hR : 0 ≤ R) (q : Nat)
    (h : holSqrtDistLe R ((fp64N q : Nat) : Rat) ((fp64N (fp64NearestSqrt R) : Nat) : Rat)) :
    q = fp64NearestSqrt R ∨ (fp64NearestSqrt R % 2 = 0 ∧ q % 2 = 1) := by
  have ⟨hlo, hhi⟩ := fp64BracketSqrt hR
  have hcase := fp64NearestSqrt_cases (R := R)
  generalize fp64NearestSqrt R = a at *
  generalize fp64Bracket (Nat.sqrt R.floor.toNat) = p at *
  have hlohi := fp64N_cast_lt' (Nat.lt_succ_self p)
  unfold holSqrtDistLe at h
  rcases h with h | ⟨hBA, hx⟩ | ⟨hAB, hx⟩
  · exact Or.inl (fp64N_inj h)
  · rcases hcase with ⟨ha, _, _⟩ | ⟨ha, hge, htie⟩
    · rw [ha] at hBA hx
      exfalso; exact holSqrtLe_Ge_lt hx hlo (by grind)
    · rw [ha] at hBA hx htie ⊢
      have hq : q ≤ p := by
        apply Nat.le_of_not_lt; intro hc
        have := fp64N_cast_le' (show p + 1 ≤ q by omega); grind
      rcases Nat.lt_or_eq_of_le hq with hq' | hq'
      · have := fp64N_cast_lt' hq'
        exfalso; exact holSqrtLe_Ge_lt hx hge (by grind)
      · subst hq'
        right; have := htie (by first | exact hx | (rw [Rat.add_comm]; exact hx)); omega
  · rcases hcase with ⟨ha, hle, htie⟩ | ⟨ha, _, _⟩
    · rw [ha] at hAB hx htie ⊢
      have hq : p + 1 ≤ q := by
        apply Nat.lt_of_not_le; intro hc
        have := fp64N_cast_le' (show q ≤ p by omega); grind
      rcases Nat.lt_or_eq_of_le hq with hq' | hq'
      · have := fp64N_cast_lt' hq'
        exfalso; exact holSqrtLe_Ge_lt hle hx (by grind)
      · subst hq'
        right; have := htie (by first | exact hx | (rw [Rat.add_comm]; exact hx)); omega
    · rw [ha] at hAB hx
      have hq : p + 1 < q := by
        apply Nat.lt_of_not_le; intro hc
        have := fp64N_cast_le' hc; grind
      have := fp64N_cast_lt' hq
      exfalso; exact holSqrtLt_Ge hhi hx (by grind)

/-- A nonpositive value as close to `sqrt R` as the nearest pattern forces
    both to be zero. -/
theorem fp64NearestSqrt_eq_neg (hR : 0 ≤ R) (q : Nat)
    (h : holSqrtDistLe R (-((fp64N q : Nat) : Rat)) ((fp64N (fp64NearestSqrt R) : Nat) : Rat)) :
    q = 0 ∧ fp64NearestSqrt R = 0 := by
  have ⟨hlo, _⟩ := fp64BracketSqrt hR
  have hcase := fp64NearestSqrt_cases (R := R)
  generalize fp64NearestSqrt R = a at *
  generalize fp64Bracket (Nat.sqrt R.floor.toNat) = p at *
  have hlohi := fp64N_cast_lt' (Nat.lt_succ_self p)
  have h0 := fp64N_cast_nonneg p
  have hq0 := fp64N_cast_nonneg q
  have ha0 := fp64N_cast_nonneg a
  unfold holSqrtDistLe at h
  rcases h with h | ⟨hBA, hx⟩ | ⟨hAB, _⟩
  · have hq : ((fp64N q : Nat) : Rat) = 0 := by grind
    have ha : ((fp64N a : Nat) : Rat) = 0 := by grind
    exact ⟨fp64N_eq_zero.1 (by exact_mod_cast hq), fp64N_eq_zero.1 (by exact_mod_cast ha)⟩
  · rcases hcase with ⟨ha, _, _⟩ | ⟨ha, hge, htie⟩
    · rw [ha] at hBA hx
      exfalso; exact holSqrtLe_Ge_lt hx hlo (by grind)
    · rw [ha] at hBA hx htie
      exfalso
      rcases Rat.le_iff_lt_or_eq.1 (show (-((fp64N q : Nat) : Rat) + ((fp64N (p + 1) : Nat) : Rat)) / 2 ≤
          (((fp64N p : Nat) : Rat) + ((fp64N (p + 1) : Nat) : Rat)) / 2 by grind) with hlt | heq
      · exact holSqrtLe_Ge_lt hx hge hlt
      · rw [heq] at hx
        have hp0 : ((fp64N p : Nat) : Rat) = 0 := by grind
        have hp : p = 0 := fp64N_eq_zero.1 (by exact_mod_cast hp0)
        have := htie hx; omega
  · exfalso; grind

end NearestSqrt


section Scale

variable {D : Rat}

private theorem rat_mul_le_mul_right_iff {a b : Rat} (hD : 0 < D) : a * D ≤ b * D ↔ a ≤ b := by
  constructor
  · intro h; exact Rat.le_of_mul_le_mul_right h hD
  · intro h; exact Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hD)

private theorem rat_mul_eq_mul_right_iff {a b : Rat} (hD : 0 < D) : a * D = b * D ↔ a = b := by
  constructor
  · intro h
    have h1 : a ≤ b := (rat_mul_le_mul_right_iff hD).1 (by rw [h]; exact Rat.le_refl)
    have h2 : b ≤ a := (rat_mul_le_mul_right_iff hD).1 (by rw [h]; exact Rat.le_refl)
    exact Rat.le_antisymm h1 h2
  · intro h; rw [h]

private theorem sq_scale (m r D : Rat) :
    (m * D) * (m * D) = (m * m) * (D * D) ∧ r * (D * D) = r * (D * D) := by
  constructor <;> grind

theorem holSqrtLe_scale (hD : 0 < D) (r m : Rat) :
    holSqrtLe r m ↔ holSqrtLe (r * (D * D)) (m * D) := by
  have hDD : 0 < D * D := Rat.mul_pos hD hD
  unfold holSqrtLe
  rw [(sq_scale m r D).1]
  have e1 : (0 : Rat) ≤ m * D ↔ 0 ≤ m := by
    have := rat_mul_le_mul_right_iff (a := 0) (b := m) hD; simpa using this
  rw [e1, rat_mul_le_mul_right_iff hDD]

theorem holSqrtGe_scale (hD : 0 < D) (r m : Rat) :
    holSqrtGe r m ↔ holSqrtGe (r * (D * D)) (m * D) := by
  have hDD : 0 < D * D := Rat.mul_pos hD hD
  unfold holSqrtGe
  rw [(sq_scale m r D).1]
  have e1 : m * D ≤ 0 ↔ m ≤ 0 := by
    have := rat_mul_le_mul_right_iff (a := m) (b := 0) hD; simpa using this
  rw [e1, rat_mul_le_mul_right_iff hDD]

theorem holSqrtLt_scale (hD : 0 < D) (r m : Rat) :
    holSqrtLt r m ↔ holSqrtLt (r * (D * D)) (m * D) := by
  have hDD : 0 < D * D := Rat.mul_pos hD hD
  unfold holSqrtLt
  rw [(sq_scale m r D).1]
  have e1 : (0 : Rat) < m * D ↔ 0 < m := by
    have := Rat.mul_lt_mul_right (a := 0) (b := m) hD; simpa using this
  rw [e1, Rat.mul_lt_mul_right hDD]

theorem holSqrtDistLe_scale (hD : 0 < D) (r A B : Rat) :
    holSqrtDistLe r A B ↔ holSqrtDistLe (r * (D * D)) (A * D) (B * D) := by
  unfold holSqrtDistLe
  have hmid : (A * D + B * D) / 2 = (A + B) / 2 * D := by grind
  rw [hmid, ← holSqrtLe_scale hD, ← holSqrtGe_scale hD, rat_mul_eq_mul_right_iff hD,
    Rat.mul_lt_mul_right hD, Rat.mul_lt_mul_right hD]

end Scale

/-- A binary64 float's value scaled by `2^1074`. -/
theorem holFloatToReal_fp64_scaled (f : HolFloat 52 11) :
    holFloatToReal f * 2 ^ 1074 =
      if f.sign = 1 then -((fp64N (fp64Pat f) : Nat) : Rat) else ((fp64N (fp64Pat f) : Nat) : Rat) := by
  have hD := fp64_D_pos
  rw [holFloatToReal_fp64]
  generalize (2 : Rat) ^ 1074 = D at *
  split <;> grind


theorem fp64NearestSqrt_lt {R : Rat} (hR : 0 ≤ R)
    (hth : holSqrtLt R (((fp64N fp64MaxPat : Nat) : Rat) + ((fp64Step fp64MaxPat : Nat) : Rat) / 2)) :
    fp64NearestSqrt R < 2047 * 2 ^ 52 := by
  have ⟨hlo, _⟩ := fp64BracketSqrt hR
  have hcase := fp64NearestSqrt_cases (R := R)
  generalize fp64NearestSqrt R = a at *
  generalize fp64Bracket (Nat.sqrt R.floor.toNat) = p at *
  have hsucc : ((fp64N (fp64MaxPat + 1) : Nat) : Rat) =
      ((fp64N fp64MaxPat : Nat) : Rat) + ((fp64Step fp64MaxPat : Nat) : Rat) := by
    rw [fp64N_succ]; push_cast; rfl
  have hstep : (0 : Rat) < ((fp64Step fp64MaxPat : Nat) : Rat) := by exact_mod_cast fp64Step_pos _
  have hmax : fp64MaxPat + 1 = 2047 * 2 ^ 52 := by decide
  have hp : p ≤ fp64MaxPat := by
    apply Nat.le_of_not_lt; intro hlt
    have := fp64N_cast_le' (show fp64MaxPat + 1 ≤ p by omega)
    exact holSqrtLt_Ge hth hlo (by grind)
  rcases hcase with ⟨ha, _, _⟩ | ⟨ha, hge, _⟩
  · rw [ha]; omega
  · by_cases hpm : p = fp64MaxPat
    · rw [hpm] at hge
      exfalso; exact holSqrtLt_Ge hth hge (by grind)
    · rw [ha]; omega

/-- HOL's `round roundTiesToEven (sqrt r)` choice predicate. -/
def fp64RtePredSqrt (r : Rat) (c : HolFloat 52 11) : Prop :=
  holIsClosestSqrt (fun a : HolFloat 52 11 => holFloatIsFinite a = true) r c ∧
    ∀ b : HolFloat 52 11,
      holIsClosestSqrt (fun a : HolFloat 52 11 => holFloatIsFinite a = true) r b ∧
        b.significand.getLsbD 0 = false → c.significand.getLsbD 0 = false

/-- The core of the sqrt conformance proof for `0 ≤ r` below the threshold. -/
theorem fp64_rte_sqrt_core {r : Rat} (hr : 0 ≤ r)
    (hth : ¬ holSqrtGe r (holFloatThreshold 52 11)) :
    let a := fp64OfPat false (fp64NearestSqrt (r * (2 ^ 1074 * 2 ^ 1074)))
    fp64RtePredSqrt r a ∧
      ∀ c, fp64RtePredSqrt r c →
        holFloatIsZero c = holFloatIsZero a ∧ (holFloatIsZero a = false → c = a) := by
  intro a
  have hD := fp64_D_pos
  have hR : 0 ≤ r * (2 ^ 1074 * 2 ^ 1074) := Rat.mul_nonneg hr (Rat.le_of_lt (Rat.mul_pos hD hD))
  have hthLt : holSqrtLt r (holFloatThreshold 52 11) := by
    unfold holSqrtGe at hth; unfold holSqrtLt
    exact ⟨Rat.not_le.1 (fun h => hth (Or.inl h)), Rat.not_le.1 (fun h => hth (Or.inr h))⟩
  have hthR := (holSqrtLt_scale hD r _).1 hthLt
  rw [fp64_threshold_scaled] at hthR
  -- scaled distance comparisons
  have hscale : ∀ f g : HolFloat 52 11,
      holSqrtDistLe r (holFloatToReal f) (holFloatToReal g) ↔
        holSqrtDistLe (r * (2 ^ 1074 * 2 ^ 1074))
          (if f.sign = 1 then -((fp64N (fp64Pat f) : Nat) : Rat) else ((fp64N (fp64Pat f) : Nat) : Rat))
          (if g.sign = 1 then -((fp64N (fp64Pat g) : Nat) : Rat) else ((fp64N (fp64Pat g) : Nat) : Rat)) := by
    intro f g
    rw [holSqrtDistLe_scale hD, holFloatToReal_fp64_scaled, holFloatToReal_fp64_scaled]
  generalize hRd : r * (2 ^ 1074 * 2 ^ 1074) = R at hR hthR hscale
  have hn := fp64NearestSqrt_lt hR hthR
  have hpa : fp64Pat a = fp64NearestSqrt R := by
    show fp64Pat (fp64OfPat false (fp64NearestSqrt (r * (2 ^ 1074 * 2 ^ 1074)))) = _
    rw [hRd]; exact fp64Pat_ofPat false (by omega)
  have hsa : ¬ a.sign = 1 := by
    intro h
    have h0 : a.sign = 0 := rfl
    rw [h0] at h; exact absurd h (by decide)
  have hafin : holFloatIsFinite a = true := (fp64_isFinite_iff a).2 (by rw [hpa]; exact hn)
  have hlsba : a.significand.getLsbD 0 = decide (fp64NearestSqrt R % 2 = 1) := by
    show (fp64OfPat false (fp64NearestSqrt (r * (2 ^ 1074 * 2 ^ 1074)))).significand.getLsbD 0 = _
    rw [fp64OfPat_lsb, hRd]
  have hle : ∀ b : HolFloat 52 11, holSqrtDistLe r (holFloatToReal a) (holFloatToReal b) := by
    intro b
    rw [hscale, if_neg hsa, hpa]
    split
    · exact fp64NearestSqrt_le_neg hR _
    · exact fp64NearestSqrt_le_pos hR _
  have hclosest : holIsClosestSqrt (fun a : HolFloat 52 11 => holFloatIsFinite a = true) r a :=
    ⟨hafin, fun b _ => hle b⟩
  have heq : ∀ c : HolFloat 52 11,
      holIsClosestSqrt (fun a : HolFloat 52 11 => holFloatIsFinite a = true) r c →
      (c.sign = 1 → fp64Pat c = 0 ∧ fp64NearestSqrt R = 0) ∧
      (¬ c.sign = 1 → fp64Pat c = fp64NearestSqrt R ∨
        (fp64NearestSqrt R % 2 = 0 ∧ fp64Pat c % 2 = 1)) := by
    intro c ⟨_, hc⟩
    have h1 := hc a hafin
    rw [hscale, if_neg hsa, hpa] at h1
    constructor
    · intro hs; rw [if_pos hs] at h1; exact fp64NearestSqrt_eq_neg hR _ h1
    · intro hs; rw [if_neg hs] at h1; exact fp64NearestSqrt_eq_pos hR _ h1
  have hPa : fp64RtePredSqrt r a := by
    refine ⟨hclosest, fun b ⟨hb, hbe⟩ => ?_⟩
    rw [hlsba]
    by_cases hn2 : fp64NearestSqrt R % 2 = 0
    · simp [hn2]
    · have ⟨hneg, hpos⟩ := heq b hb
      by_cases hs : b.sign = 1
      · have := (hneg hs).2; omega
      · rcases hpos hs with hbp | ⟨h, _⟩
        · have hba : b = a := by
            rw [fp64OfPat_eq_of_pat b hs, hbp]
            show fp64OfPat false (fp64NearestSqrt R) =
              fp64OfPat false (fp64NearestSqrt (r * (2 ^ 1074 * 2 ^ 1074)))
            rw [hRd]
          rw [hba, hlsba] at hbe; exact hbe
        · exact absurd h hn2
  refine ⟨hPa, fun c ⟨hc, hct⟩ => ?_⟩
  have hcfin : holFloatIsFinite c = true := hc.1
  have hza : holFloatIsZero a = true ↔ fp64NearestSqrt R = 0 := by
    rw [fp64_isZero_iff a hafin, hpa]
  have hzc : holFloatIsZero c = true ↔ fp64Pat c = 0 := fp64_isZero_iff c hcfin
  have ⟨hneg, hpos⟩ := heq c hc
  by_cases hs : c.sign = 1
  · have ⟨hc0, hn0⟩ := hneg hs
    have hzc' : holFloatIsZero c = true := hzc.2 hc0
    have hza' : holFloatIsZero a = true := hza.2 hn0
    refine ⟨by rw [hzc', hza'], fun h => by rw [hza'] at h; exact absurd h (by decide)⟩
  · rcases hpos hs with hcp | ⟨hn2, hc2⟩
    · have hca : c = a := by
        rw [fp64OfPat_eq_of_pat c hs, hcp]
        show fp64OfPat false (fp64NearestSqrt R) =
          fp64OfPat false (fp64NearestSqrt (r * (2 ^ 1074 * 2 ^ 1074)))
        rw [hRd]
      exact ⟨by rw [hca], fun _ => hca⟩
    · exfalso
      have hae : a.significand.getLsbD 0 = false := by rw [hlsba]; simp [hn2]
      have := hct a ⟨hclosest, hae⟩
      rw [fp64OfPat_eq_of_pat c hs, fp64OfPat_lsb] at this
      simp [hc2] at this

/-- Computable binary64 `float_round roundTiesToEven toneg (sqrt r)` for a
    rational `r ≥ 0`. -/
def holFp64SqrtRoundRte (toneg : Bool) (r : Rat) : HolFloat 52 11 :=
  if holSqrtLe r (-holFloatThreshold 52 11) then holFloatMinusInfinity 52 11
  else if holSqrtGe r (holFloatThreshold 52 11) then holFloatPlusInfinity 52 11
  else
    let a := fp64OfPat false (fp64NearestSqrt (r * (2 ^ 1074 * 2 ^ 1074)))
    if holFloatIsZero a then
      (if toneg then holFloatMinusZero 52 11 else holFloatPlusZero 52 11)
    else a

private theorem fp64_zero_select' {c a z : HolFloat 52 11}
    (h1 : holFloatIsZero c = holFloatIsZero a) (h2 : holFloatIsZero a = false → c = a) :
    (if holFloatIsZero c then z else c) = (if holFloatIsZero a then z else a) := by
  rw [h1]
  cases ha : holFloatIsZero a
  · rw [h2 ha]
  · rfl

/-- The computable sqrt rounding agrees with the rational-cut rendering of
    HOL's choice-based `float_round roundTiesToEven toneg (sqrt r)` at binary64,
    for every rational `r ≥ 0`. -/
theorem holFloatRoundSqrt_rte_fp64 (toneg : Bool) {r : Rat} (hr : 0 ≤ r) :
    (holFloatRoundSqrt .roundTiesToEven toneg r : HolFloat 52 11) =
      holFp64SqrtRoundRte toneg r := by
  unfold holFloatRoundSqrt holRoundSqrt holFp64SqrtRoundRte
  simp only
  by_cases h1 : holSqrtLe r (-holFloatThreshold 52 11)
  · rw [if_pos h1, if_pos h1]
    have : holFloatIsZero (holFloatMinusInfinity 52 11) = false := by decide +kernel
    rw [this]; rfl
  rw [if_neg h1, if_neg h1]
  by_cases h2 : holSqrtGe r (holFloatThreshold 52 11)
  · rw [if_pos h2, if_pos h2]
    have : holFloatIsZero (holFloatPlusInfinity 52 11) = false := by decide +kernel
    rw [this]; rfl
  rw [if_neg h2, if_neg h2]
  obtain ⟨hPa, hall⟩ := fp64_rte_sqrt_core hr h2
  generalize fp64OfPat false (fp64NearestSqrt (r * (2 ^ 1074 * 2 ^ 1074))) = a at hPa hall
  have hc : fp64RtePredSqrt r (holClosestSuchSqrt (fun a => a.significand.getLsbD 0 = false)
      (fun a => holFloatIsFinite a = true) r) :=
    Classical.epsilon_spec (p := fun c => fp64RtePredSqrt r c) ⟨a, hPa⟩
  generalize holClosestSuchSqrt (t := 52) (w := 11) _ _ r = c at hc ⊢
  have ⟨hz, hne⟩ := hall _ hc
  exact fp64_zero_select' hz hne


/-- HOL `float_sqrt roundTiesToEven` at binary64 with the computable rounding. -/
noncomputable def holFloatSqrtRte64 (x : HolFloat 52 11) : HolFloat 52 11 :=
  if x.sign = 0 then
    match holFloatValue x with
    | .nan => holFloatSomeQnan (.fpSqrt .roundTiesToEven x)
    | .infinity => holFloatPlusInfinity 52 11
    | .float r => holFp64SqrtRoundRte false r
  else if x = holFloatMinusZero 52 11 then holFloatMinusZero 52 11
  else holFloatSomeQnan (.fpSqrt .roundTiesToEven x)

/-- A positive-sign finite binary64 float has a nonnegative value. -/
theorem fp64_value_nonneg {x : HolFloat 52 11} {r : Rat} (hs : x.sign = 0)
    (hv : holFloatValue x = .float r) : 0 ≤ r := by
  have hr : holFloatToReal x = r := by
    unfold holFloatValue at hv; split at hv
    · split at hv <;> simp at hv
    · simpa using hv
  rw [← hr, holFloatToReal_fp64]
  have h1 : ¬ x.sign = 1 := by rw [hs]; decide
  rw [if_neg h1]
  have hD := fp64_D_pos
  have hN := fp64N_cast_nonneg (fp64Pat x)
  generalize (2 : Rat) ^ 1074 = D at *
  have : (1 : Rat) * ((fp64N (fp64Pat x) : Nat) : Rat) / D =
      ((fp64N (fp64Pat x) : Nat) : Rat) * D⁻¹ := by grind
  rw [this]
  exact Rat.mul_nonneg hN (Rat.le_of_lt (Rat.inv_pos.2 hD))

theorem holFloatSqrt_rte64 (x : HolFloat 52 11) :
    (holFloatSqrt .roundTiesToEven x).2 = holFloatSqrtRte64 x := by
  unfold holFloatSqrt holFloatSqrtRte64
  by_cases hs : x.sign = 0
  · rw [if_pos hs, if_pos hs]
    cases hv : holFloatValue x with
    | nan => rfl
    | infinity => rfl
    | float r =>
      simp only
      show (holFloatRoundSqrt .roundTiesToEven false r : HolFloat 52 11) = _
      exact holFloatRoundSqrt_rte_fp64 false (fp64_value_nonneg hs hv)
  · rw [if_neg hs, if_neg hs]
    split <;> rfl

/-- `fp64_sqrt roundTiesToEven` through the computable rounding. -/
theorem holFp64Sqrt_rte (a : BitVec 64) :
    holFp64Sqrt .roundTiesToEven a = holFloatToFp64 (holFloatSqrtRte64 (holFp64ToFloat a)) := by
  unfold holFp64Sqrt; rw [holFloatSqrt_rte64]

end Flapjack
