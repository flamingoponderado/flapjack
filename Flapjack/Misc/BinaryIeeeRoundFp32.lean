import Flapjack.Misc.BinaryIeeeRound

/-!
# Complete computable binary32 nearest-even rounding agreement

Flapjack proof infrastructure: HOL specifies `round`/`float_round` by choice
in `HOL/src/floating-point/binary_ieeeScript.sml:347-443,509-518`; it does
not name this computable algorithm or its agreement theorem. This adapts the
reviewed binary64 pattern/bracket proof to the distinct binary32 format:
23 significand bits, 8 exponent bits, 31 magnitude bits, and subnormal unit
2^-149. Every rational input and both requested zero signs are covered,
including finite ties and threshold infinities. The kernel theorem proves
agreement with the existing rational rendering, not cross-assistant equivalence
with HOL reals; SOUNDNESS item8 remains unchanged. Helpers are scoped to avoid
shadowing or duplicating the public binary64 declarations.
-/

namespace Flapjack.Binary32Rounding

/-- The 31-bit pattern `exponent * 2^23 + significand` of a binary32 float. -/
def fp32Pat (f : HolFloat 23 8) : Nat := f.exponent.toNat * 2 ^ 23 + f.significand.toNat

/-- The magnitude of pattern `q` in units of `2^-149`. -/
def fp32N (q : Nat) : Nat := if q < 2 ^ 23 then q else (2 ^ 23 + q % 2 ^ 23) * 2 ^ (q / 2 ^ 23 - 1)

theorem fp32Pat_div (f : HolFloat 23 8) : fp32Pat f / 2 ^ 23 = f.exponent.toNat := by
  have := f.significand.isLt
  unfold fp32Pat; omega

theorem fp32Pat_mod (f : HolFloat 23 8) : fp32Pat f % 2 ^ 23 = f.significand.toNat := by
  have := f.significand.isLt
  unfold fp32Pat; omega

/-- A binary32 float's value is `±fp32N (pattern) / 2^149`. -/
theorem holFloatToReal_fp32 (f : HolFloat 23 8) :
    holFloatToReal f = (if f.sign = 1 then -1 else 1) * ((fp32N (fp32Pat f) : Nat) : Rat) / 2 ^ 149 := by
  have hs : f.significand.toNat < 2 ^ 23 := f.significand.isLt
  have hsign : (-1 : Rat) ^ f.sign.toNat = (if f.sign = 1 then -1 else 1) := by
    have : f.sign = 0 ∨ f.sign = 1 := by
      have h := f.sign.isLt
      rcases Nat.lt_succ_iff.mp h |> Nat.le_one_iff_eq_zero_or_eq_one.mp with h0 | h1
      · left; exact BitVec.eq_of_toNat_eq (by simp [h0])
      · right; exact BitVec.eq_of_toNat_eq (by simp [h1])
    rcases this with h | h <;> rw [h] <;> decide
  unfold holFloatToReal fp32N
  rw [hsign]
  by_cases he : f.exponent = 0
  · have he' : f.exponent.toNat = 0 := by simp [he]
    have hlt : fp32Pat f < 2 ^ 23 := by unfold fp32Pat; omega
    have hp : fp32Pat f = f.significand.toNat := by unfold fp32Pat; omega
    simp only [he, if_true, hp, holFloatBias]
    grind
  · have hne : f.exponent.toNat ≠ 0 := fun h => he (BitVec.eq_of_toNat_eq (by simpa using h))
    have hge : ¬ fp32Pat f < 2 ^ 23 := by unfold fp32Pat; have := Nat.pos_of_ne_zero hne; omega
    simp only [he, if_false, hge, fp32Pat_div, fp32Pat_mod, holFloatBias]
    obtain ⟨k, hk⟩ : ∃ k, f.exponent.toNat = k + 1 := ⟨f.exponent.toNat - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    push_cast
    grind

/-- The gap from pattern `q` to pattern `q + 1`. -/
def fp32Step (q : Nat) : Nat := if q < 2 ^ 23 then 1 else 2 ^ (q / 2 ^ 23 - 1)

theorem fp32Step_pos (q : Nat) : 0 < fp32Step q := by
  unfold fp32Step; split
  · decide
  · exact Nat.two_pow_pos _

/-- Division and remainder of `e * M + s` by `M` when `s < M`. -/
theorem fp32_divmod {M e s : Nat} (hs : s < M) : (e * M + s) / M = e ∧ (e * M + s) % M = s := by
  have hM : 0 < M := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hs, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

theorem fp32N_succ (q : Nat) : fp32N (q + 1) = fp32N q + fp32Step q := by
  unfold fp32N fp32Step
  generalize hM : (2 : Nat) ^ 23 = M
  have hMpos : 2 ≤ M := by rw [← hM]; decide
  by_cases h1 : q + 1 < M
  · have h0 : q < M := by omega
    simp [h1, h0]
  · by_cases h0 : q < M
    · have hq : q + 1 = 1 * M + 0 := by omega
      have ⟨hd, hm⟩ := fp32_divmod (e := 1) (show 0 < M by omega)
      rw [if_neg h1, if_pos h0, if_pos h0, hq, hd, hm]
      omega
    · simp only [h1, h0, if_false]
      obtain ⟨e, s, hs, rfl⟩ : ∃ e s, s < M ∧ q = e * M + s :=
        ⟨q / M, q % M, Nat.mod_lt _ (by omega), (Nat.div_add_mod' q M).symm⟩
      have ⟨hd, hm⟩ := fp32_divmod (e := e) hs
      have he : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with h | h
        · subst h; simp at h0; omega
        · exact h
      rw [hd, hm]
      by_cases hs1 : s + 1 < M
      · have ⟨hd', hm'⟩ := fp32_divmod (e := e) hs1
        rw [Nat.add_assoc, hd', hm', Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.one_mul]
        omega
      · have hs' : s + 1 = M := by omega
        have hq : e * M + s + 1 = (e + 1) * M + 0 := by rw [Nat.add_mul]; omega
        have ⟨hd', hm'⟩ := fp32_divmod (e := e + 1) (show 0 < M by omega)
        rw [hq, hd', hm']
        obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
        simp only [Nat.add_sub_cancel, Nat.pow_succ, Nat.add_zero]
        have hsM : M + s + 1 = 2 * M := by omega
        calc M * (2 ^ k * 2) = 2 * M * 2 ^ k := by
                rw [Nat.mul_comm 2 M, Nat.mul_assoc, Nat.mul_comm 2]
          _ = (M + s + 1) * 2 ^ k := by rw [hsM]
          _ = (M + s) * 2 ^ k + 2 ^ k := by rw [Nat.add_mul (M + s) 1, Nat.one_mul]

theorem fp32N_mono {q r : Nat} (h : q ≤ r) : fp32N q ≤ fp32N r := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [fp32N_succ]; omega

theorem fp32N_strictMono {q r : Nat} (h : q < r) : fp32N q < fp32N r := by
  have h1 := fp32N_succ q
  have h2 := fp32Step_pos q
  have h3 := fp32N_mono (show q + 1 ≤ r from h)
  omega


/-- The largest pattern whose value `N` is at most `k`: `k` itself in the
    subnormal range, otherwise exponent `log2 k - 22` and the top 24 bits of
    `k`. -/
def fp32Bracket (k : Nat) : Nat :=
  if k < 2 ^ 23 then k
  else (k.log2 - 22) * 2 ^ 23 + (k / 2 ^ (k.log2 - 23) - 2 ^ 23)

theorem fp32Bracket_spec (k : Nat) :
    fp32N (fp32Bracket k) ≤ k ∧ k < fp32N (fp32Bracket k + 1) := by
  rw [fp32N_succ]
  unfold fp32Bracket
  by_cases hk : k < 2 ^ 23
  · rw [if_pos hk]
    unfold fp32N fp32Step
    rw [if_pos hk, if_pos hk]
    omega
  · rw [if_neg hk]
    have hk0 : k ≠ 0 := by intro h; subst h; exact hk (by decide)
    have hL : 23 ≤ k.log2 := (Nat.le_log2 hk0).2 (by omega)
    obtain ⟨j, hj⟩ : ∃ j, k.log2 = 23 + j := ⟨k.log2 - 23, by omega⟩
    have hlo : 2 ^ (23 + j) ≤ k := hj ▸ Nat.log2_self_le hk0
    have hhi : k < 2 ^ (23 + j + 1) := hj ▸ Nat.lt_log2_self
    have hlo2 : 2 ^ 23 * 2 ^ j ≤ k := by rw [← Nat.pow_add]; exact hlo
    have hhi2 : k < 2 ^ 24 * 2 ^ j := by
      rw [← Nat.pow_add, show 24 + j = 23 + j + 1 by omega]; exact hhi
    rw [hj, show 23 + j - 22 = j + 1 by omega, show 23 + j - 23 = j by omega]
    clear hlo hhi
    generalize hS : (2 : Nat) ^ j = S at *
    have hSpos : 0 < S := by rw [← hS]; exact Nat.two_pow_pos _
    have hlo' : 2 ^ 23 * S ≤ k := hlo2
    have hhi' : k < 2 ^ 24 * S := hhi2
    have hm1 : 2 ^ 23 ≤ k / S := (Nat.le_div_iff_mul_le hSpos).2 (by rw [Nat.mul_comm] at hlo'; omega)
    have hm2 : k / S < 2 ^ 24 := (Nat.div_lt_iff_lt_mul hSpos).2 (by rw [Nat.mul_comm] at hhi'; omega)
    have hsig : k / S - 2 ^ 23 < 2 ^ 23 := by omega
    have ⟨hd, hm⟩ := fp32_divmod (e := j + 1) hsig
    have hge : ¬ (j + 1) * 2 ^ 23 + (k / S - 2 ^ 23) < 2 ^ 23 := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    unfold fp32N fp32Step
    rw [if_neg hge, if_neg hge, hd, hm, Nat.add_sub_cancel, hS,
      show 2 ^ 23 + (k / S - 2 ^ 23) = k / S by omega]
    refine ⟨Nat.div_mul_le_self k S, ?_⟩
    have := Nat.lt_mul_div_succ k hSpos
    rw [Nat.mul_comm S, Nat.add_mul, Nat.one_mul] at this
    exact this


/-- The binary32 float with the given sign and 31-bit pattern. -/
def fp32OfPat (neg : Bool) (q : Nat) : HolFloat 23 8 :=
  { sign := if neg then 1 else 0, exponent := BitVec.ofNat 8 (q / 2 ^ 23),
    significand := BitVec.ofNat 23 (q % 2 ^ 23) }

theorem fp32Pat_lt (f : HolFloat 23 8) : fp32Pat f < 2 ^ 31 := by
  have h1 := f.exponent.isLt
  have h2 := f.significand.isLt
  unfold fp32Pat
  have : f.exponent.toNat * 2 ^ 23 ≤ (2 ^ 8 - 1) * 2 ^ 23 := Nat.mul_le_mul_right _ (by omega)
  omega

theorem fp32Pat_ofPat (neg : Bool) {q : Nat} (hq : q < 2 ^ 31) : fp32Pat (fp32OfPat neg q) = q := by
  unfold fp32Pat fp32OfPat
  have hd : q / 2 ^ 23 < 2 ^ 8 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd, Nat.mod_mod]
  exact Nat.div_add_mod' q (2 ^ 23)

theorem fp32OfPat_pat (f : HolFloat 23 8) : fp32OfPat (decide (f.sign = 1)) (fp32Pat f) = f := by
  obtain ⟨s, e, m⟩ := f
  have hsig : fp32OfPat (decide (s = 1)) (fp32Pat ⟨s, e, m⟩) =
      ⟨if decide (s = 1) then 1 else 0, BitVec.ofNat 8 e.toNat, BitVec.ofNat 23 m.toNat⟩ := by
    unfold fp32OfPat
    rw [fp32Pat_div, fp32Pat_mod]
  rw [hsig]
  have hs : ∀ s : BitVec 1, (if decide (s = 1) = true then (1 : BitVec 1) else 0) = s := by decide
  rw [hs s]
  simp

theorem fp32_isFinite_iff (f : HolFloat 23 8) :
    holFloatIsFinite f = true ↔ fp32Pat f < 255 * 2 ^ 23 := by
  have h1 := f.exponent.isLt
  have h2 := f.significand.isLt
  have hne : f.exponent ≠ BitVec.allOnes 8 ↔ f.exponent.toNat ≠ 255 := by
    constructor
    · intro h h'; exact h (BitVec.eq_of_toNat_eq (by simp [h']))
    · intro h h'; exact h (by simp [h'])
  have hfin : holFloatIsFinite f = true ↔ f.exponent ≠ BitVec.allOnes 8 := by
    unfold holFloatIsFinite holFloatValue
    by_cases he : f.exponent = BitVec.allOnes 8
    · rw [if_pos he]
      by_cases hs : f.significand = 0
      · rw [if_pos hs]; simp [he]
      · rw [if_neg hs]; simp [he]
    · rw [if_neg he]
      simpa using he
  rw [hfin, hne]
  unfold fp32Pat
  constructor
  · intro h
    have : f.exponent.toNat ≤ 254 := by omega
    have : f.exponent.toNat * 2 ^ 23 ≤ 254 * 2 ^ 23 := Nat.mul_le_mul_right _ this
    omega
  · intro h h'
    rw [h'] at h
    omega

theorem fp32OfPat_lsb (neg : Bool) (q : Nat) :
    (fp32OfPat neg q).significand.getLsbD 0 = decide (q % 2 = 1) := by
  unfold fp32OfPat
  simp only [BitVec.getLsbD_ofNat, Nat.testBit_zero]
  have : q % 2 ^ 23 % 2 = q % 2 := Nat.mod_mod_of_dvd q (by decide)
  simp [this]

theorem fp32N_eq_zero {q : Nat} : fp32N q = 0 ↔ q = 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · exact h0
    · have := fp32N_strictMono h0
      have h00 : fp32N 0 = 0 := by decide
      omega
  · intro h; subst h; decide


/-- The pattern nearest to `X ≥ 0` (in units of `2^-149`), ties to the even
    pattern, among the two patterns bracketing `X`. -/
def fp32Nearest (X : Rat) : Nat :=
  let p := fp32Bracket X.floor.toNat
  let lo : Rat := (fp32N p : Rat)
  let hi : Rat := (fp32N (p + 1) : Rat)
  if X - lo < hi - X then p
  else if hi - X < X - lo then p + 1
  else if p % 2 = 0 then p else p + 1

theorem fp32Bracket_rat {X : Rat} (hX : 0 ≤ X) :
    ((fp32N (fp32Bracket X.floor.toNat) : Nat) : Rat) ≤ X ∧
      X < ((fp32N (fp32Bracket X.floor.toNat + 1) : Nat) : Rat) := by
  have ⟨h1, h2⟩ := fp32Bracket_spec X.floor.toNat
  have hfl : 0 ≤ X.floor := Rat.le_floor_iff.2 (by simpa using hX)
  have hk : ((X.floor.toNat : Nat) : Rat) = (X.floor : Rat) := by
    have h := congrArg (fun z : Int => (z : Rat)) (Int.toNat_of_nonneg hfl)
    rw [← h]
    exact (Rat.intCast_natCast _).symm
  have hle := Rat.floor_le X
  have hlt := Rat.lt_floor_add_one X
  have c1 : ((fp32N (fp32Bracket X.floor.toNat) : Nat) : Rat) ≤ ((X.floor.toNat : Nat) : Rat) := by
    exact_mod_cast h1
  have c2 : ((X.floor.toNat : Nat) : Rat) + 1 ≤ ((fp32N (fp32Bracket X.floor.toNat + 1) : Nat) : Rat) := by
    exact_mod_cast h2
  push_cast at hlt
  constructor <;> grind


section Nearest

variable {X : Rat}

/-- Distance, in units of `2^-149`, from `X` to the value of pattern `q`. -/
def fp32Dist (X : Rat) (q : Nat) : Rat := holRatAbs (((fp32N q : Nat) : Rat) - X)

theorem fp32Nearest_cases (hX : 0 ≤ X) :
    (fp32Nearest X = fp32Bracket X.floor.toNat ∨ fp32Nearest X = fp32Bracket X.floor.toNat + 1) ∧
      fp32Dist X (fp32Nearest X) ≤ X - ((fp32N (fp32Bracket X.floor.toNat) : Nat) : Rat) ∧
      fp32Dist X (fp32Nearest X) ≤ ((fp32N (fp32Bracket X.floor.toNat + 1) : Nat) : Rat) - X ∧
      (X - ((fp32N (fp32Bracket X.floor.toNat) : Nat) : Rat) =
          ((fp32N (fp32Bracket X.floor.toNat + 1) : Nat) : Rat) - X → fp32Nearest X % 2 = 0) := by
  have ⟨h1, h2⟩ := fp32Bracket_rat hX
  unfold fp32Nearest fp32Dist holRatAbs
  simp only
  generalize fp32Bracket X.floor.toNat = p at *
  generalize hlo : ((fp32N p : Nat) : Rat) = lo at *
  generalize hhi : ((fp32N (p + 1) : Nat) : Rat) = hi at *
  by_cases c1 : X - lo < hi - X
  · simp only [c1, if_true, hlo]
    refine ⟨by first | exact Or.inl trivial | exact Or.inl rfl | trivial, ?_, ?_, fun h => by exfalso; grind⟩ <;> split <;> grind
  · by_cases c2 : hi - X < X - lo
    · simp only [c1, c2, if_true, if_false, hhi]
      refine ⟨by first | exact Or.inr trivial | exact Or.inr rfl | trivial, ?_, ?_, fun h => by exfalso; grind⟩ <;> split <;> grind
    · simp only [c1, c2, if_false]
      by_cases hp : p % 2 = 0
      · simp only [hp, if_true, hlo]
        refine ⟨by first | exact Or.inl trivial | exact Or.inl rfl | trivial, ?_, ?_, fun _ => by first | trivial | exact hp⟩ <;> split <;> grind
      · simp only [hp, if_false, hhi]
        refine ⟨by first | exact Or.inr trivial | exact Or.inr rfl | trivial, ?_, ?_, fun _ => by first | trivial | omega⟩ <;> split <;> grind

theorem fp32Nearest_succ_le (_hX : 0 ≤ X)
    (h : fp32Nearest X = fp32Bracket X.floor.toNat + 1) :
    ((fp32N (fp32Bracket X.floor.toNat + 1) : Nat) : Rat) - X ≤
      X - ((fp32N (fp32Bracket X.floor.toNat) : Nat) : Rat) := by
  revert h
  unfold fp32Nearest
  simp only
  generalize fp32Bracket X.floor.toNat = p
  generalize ((fp32N p : Nat) : Rat) = lo
  generalize ((fp32N (p + 1) : Nat) : Rat) = hi
  intro h
  by_cases c1 : X - lo < hi - X
  · rw [if_pos c1] at h; omega
  · grind

private theorem fp32Dist_of_le {q : Nat} (h : ((fp32N q : Nat) : Rat) ≤ X) :
    fp32Dist X q = X - ((fp32N q : Nat) : Rat) := by
  unfold fp32Dist holRatAbs; split <;> grind

private theorem fp32Dist_of_ge {q : Nat} (h : X ≤ ((fp32N q : Nat) : Rat)) :
    fp32Dist X q = ((fp32N q : Nat) : Rat) - X := by
  unfold fp32Dist holRatAbs; split <;> grind

private theorem fp32N_cast_le {q r : Nat} (h : q ≤ r) :
    ((fp32N q : Nat) : Rat) ≤ ((fp32N r : Nat) : Rat) := by exact_mod_cast fp32N_mono h

private theorem fp32N_cast_lt {q r : Nat} (h : q < r) :
    ((fp32N q : Nat) : Rat) < ((fp32N r : Nat) : Rat) := by exact_mod_cast fp32N_strictMono h

/-- The nearest pattern is at least as close to `X` as every pattern. -/
theorem fp32Nearest_le (hX : 0 ≤ X) (q : Nat) :
    fp32Dist X (fp32Nearest X) ≤ fp32Dist X q := by
  have ⟨_, hlo, hhi, _⟩ := fp32Nearest_cases hX
  have ⟨h1, h2⟩ := fp32Bracket_rat hX
  generalize fp32Bracket X.floor.toNat = p at *
  by_cases hq : q ≤ p
  · have := fp32N_cast_le hq
    rw [fp32Dist_of_le (q := q) (by grind)]; grind
  · have := fp32N_cast_le (show p + 1 ≤ q by omega)
    rw [fp32Dist_of_ge (q := q) (by grind)]; grind

/-- No value of the opposite sign is closer than the nearest pattern. -/
theorem fp32Nearest_le_neg (hX : 0 ≤ X) (q : Nat) :
    fp32Dist X (fp32Nearest X) ≤ ((fp32N q : Nat) : Rat) + X := by
  have ⟨_, hlo, _, _⟩ := fp32Nearest_cases hX
  have h0 : (0 : Rat) ≤ ((fp32N (fp32Bracket X.floor.toNat) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  have h1 : (0 : Rat) ≤ ((fp32N q : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  grind

/-- A pattern as close as the nearest one is the nearest one, or the odd
    partner of an even nearest pattern at a tie. -/
theorem fp32Nearest_eq (hX : 0 ≤ X) (q : Nat)
    (h : fp32Dist X q = fp32Dist X (fp32Nearest X)) :
    q = fp32Nearest X ∨ (fp32Nearest X % 2 = 0 ∧ q % 2 = 1) := by
  have ⟨hcase, hlo, hhi, htie⟩ := fp32Nearest_cases hX
  have ⟨h1, h2⟩ := fp32Bracket_rat hX
  generalize fp32Nearest X = a at *
  generalize fp32Bracket X.floor.toNat = p at *
  have hp : fp32Dist X p = X - ((fp32N p : Nat) : Rat) := fp32Dist_of_le h1
  have hp1 : fp32Dist X (p + 1) = ((fp32N (p + 1) : Nat) : Rat) - X := fp32Dist_of_ge (by grind)
  by_cases hlt : q < p
  · have := fp32N_cast_lt hlt
    rw [fp32Dist_of_le (q := q) (by grind)] at h; exfalso; grind
  by_cases hgt : p + 1 < q
  · have := fp32N_cast_lt hgt
    rw [fp32Dist_of_ge (q := q) (by grind)] at h; exfalso; grind
  have hq : q = p ∨ q = p + 1 := by omega
  by_cases hqa : q = a
  · exact Or.inl hqa
  right
  rcases hq with rfl | rfl <;> rcases hcase with rfl | rfl
  · exact absurd rfl hqa
  · have ha := htie (by grind); exact ⟨ha, by omega⟩
  · have ha := htie (by grind); exact ⟨ha, by omega⟩
  · exact absurd rfl hqa

/-- A value of the opposite sign as close as the nearest pattern forces both to
    be zero. -/
theorem fp32Nearest_eq_neg (hX : 0 ≤ X) (q : Nat)
    (h : ((fp32N q : Nat) : Rat) + X = fp32Dist X (fp32Nearest X)) :
    q = 0 ∧ fp32Nearest X = 0 := by
  have ⟨_, hlo, _, _⟩ := fp32Nearest_cases hX
  have h0 : (0 : Rat) ≤ ((fp32N (fp32Bracket X.floor.toNat) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  have h1 : (0 : Rat) ≤ ((fp32N q : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  have hq0 : ((fp32N q : Nat) : Rat) = 0 := by grind
  have hp0 : ((fp32N (fp32Bracket X.floor.toNat) : Nat) : Rat) = 0 := by grind
  have hq : q = 0 := fp32N_eq_zero.1 (by exact_mod_cast hq0)
  have hp : fp32Bracket X.floor.toNat = 0 := fp32N_eq_zero.1 (by exact_mod_cast hp0)
  refine ⟨hq, ?_⟩
  have hdp : fp32Dist X (fp32Bracket X.floor.toNat) = fp32Dist X (fp32Nearest X) := by
    rw [fp32Dist_of_le (q := fp32Bracket X.floor.toNat) (by grind)]; grind
  rcases fp32Nearest_eq hX _ hdp with h' | ⟨_, h'⟩
  · rw [← h', hp]
  · rw [hp] at h'; omega

end Nearest


/-- The largest finite binary32 pattern. -/
def fp32MaxPat : Nat := 255 * 2 ^ 23 - 1

/-- `threshold` in units of `2^-149`: the largest finite value plus half its gap. -/
theorem fp32_threshold_scaled :
    holFloatThreshold 23 8 * 2 ^ 149 =
      ((fp32N fp32MaxPat : Nat) : Rat) + ((fp32Step fp32MaxPat : Nat) : Rat) / 2 := by
  decide +kernel

theorem fp32Nearest_lt {X : Rat} (hX : 0 ≤ X)
    (hth : X < ((fp32N fp32MaxPat : Nat) : Rat) + ((fp32Step fp32MaxPat : Nat) : Rat) / 2) :
    fp32Nearest X < 255 * 2 ^ 23 := by
  have ⟨hcase, _, _, _⟩ := fp32Nearest_cases hX
  have ⟨h1, h2⟩ := fp32Bracket_rat hX
  have hsucc : ((fp32N (fp32MaxPat + 1) : Nat) : Rat) =
      ((fp32N fp32MaxPat : Nat) : Rat) + ((fp32Step fp32MaxPat : Nat) : Rat) := by
    rw [fp32N_succ]; push_cast; rfl
  have hstep : (0 : Rat) < ((fp32Step fp32MaxPat : Nat) : Rat) := by exact_mod_cast fp32Step_pos _
  have hp : fp32Bracket X.floor.toNat ≤ fp32MaxPat := by
    apply Nat.le_of_not_lt; intro hlt
    have := fp32N_cast_le (show fp32MaxPat + 1 ≤ fp32Bracket X.floor.toNat by omega)
    grind
  have hmax : fp32MaxPat + 1 = 255 * 2 ^ 23 := by decide
  rcases hcase with h | h
  · rw [h]; omega
  · by_cases hpm : fp32Bracket X.floor.toNat = fp32MaxPat
    · have := fp32Nearest_succ_le hX h
      rw [hpm] at this h1 h2
      exfalso; grind
    · rw [h]; omega

/-- `2^149` is positive in `Rat`. -/
theorem fp32_D_pos : (0 : Rat) < 2 ^ 149 := Rat.pow_pos (by decide)

/-- HOL `abs` commutes with scaling by a positive factor. -/
theorem holRatAbs_mul_pos (y D : Rat) (hD : 0 < D) : holRatAbs y * D = holRatAbs (y * D) := by
  unfold holRatAbs
  by_cases hy : y < 0
  · have : y * D < 0 := by
      have := Rat.mul_lt_mul_of_pos_right hy hD; simpa using this
    rw [if_pos hy, if_pos this]; grind
  · have : ¬ y * D < 0 := by
      intro h
      have h0 : 0 ≤ y := by grind
      have := Rat.mul_le_mul_of_nonneg_right h0 (Rat.le_of_lt hD)
      simp at this; grind
    rw [if_neg hy, if_neg this]

/-- The distance from `x ≥ 0` to a binary32 float, scaled by `2^149`. -/
theorem fp32_absdist_scaled (f : HolFloat 23 8) {x : Rat} (hx : 0 ≤ x) :
    holRatAbs (holFloatToReal f - x) * 2 ^ 149 =
      if f.sign = 1 then ((fp32N (fp32Pat f) : Nat) : Rat) + x * 2 ^ 149
      else fp32Dist (x * 2 ^ 149) (fp32Pat f) := by
  have hD : (0 : Rat) < 2 ^ 149 := fp32_D_pos
  rw [holRatAbs_mul_pos _ _ hD, holFloatToReal_fp32]
  have hN : (0 : Rat) ≤ ((fp32N (fp32Pat f) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  unfold fp32Dist
  by_cases hs : f.sign = 1
  · rw [if_pos hs, if_pos hs]
    have hx' : 0 ≤ x * 2 ^ 149 := Rat.mul_nonneg hx (Rat.le_of_lt hD)
    unfold holRatAbs
    generalize (2 : Rat) ^ 149 = D at *
    have : (-1 * ((fp32N (fp32Pat f) : Nat) : Rat) / D - x) * D =
        -(((fp32N (fp32Pat f) : Nat) : Rat) + x * D) := by grind
    rw [this]; split <;> grind
  · rw [if_neg hs, if_neg hs]
    generalize (2 : Rat) ^ 149 = D at *
    congr 1
    grind

/-- A finite binary32 float is zero exactly when its pattern is zero. -/
theorem fp32_isZero_iff (f : HolFloat 23 8) (hf : holFloatIsFinite f = true) :
    holFloatIsZero f = true ↔ fp32Pat f = 0 := by
  have hfin := hf
  unfold holFloatIsFinite at hfin
  unfold holFloatIsZero
  generalize hv : holFloatValue f = v at hfin ⊢
  cases v with
  | infinity => simp at hfin
  | nan => simp at hfin
  | float r =>
    have hr : holFloatToReal f = r := by
      unfold holFloatValue at hv; split at hv
      · split at hv <;> simp at hv
      · simpa using hv
    simp only [decide_eq_true_eq]
    rw [← hr, holFloatToReal_fp32, ← fp32N_eq_zero]
    have hD : (0 : Rat) < 2 ^ 149 := fp32_D_pos
    constructor
    · intro h
      have : ((fp32N (fp32Pat f) : Nat) : Rat) = 0 := by
        by_cases hs : f.sign = 1 <;> simp [hs] at h <;> grind
      exact_mod_cast this
    · intro h; rw [h]; generalize (2 : Rat) ^ 149 = D; simp [Rat.div_def]


/-- HOL's `round roundTiesToEven` choice predicate at `x`: a closest finite
    float, preferring an even significand among the closest. -/
def fp32RtePred (x : Rat) (c : HolFloat 23 8) : Prop :=
  holIsClosest (fun a : HolFloat 23 8 => holFloatIsFinite a = true) x c ∧
    ∀ b : HolFloat 23 8, holIsClosest (fun a : HolFloat 23 8 => holFloatIsFinite a = true) x b ∧
      b.significand.getLsbD 0 = false → c.significand.getLsbD 0 = false

theorem fp32OfPat_sign_false (q : Nat) : (fp32OfPat false q).sign = 0 := rfl

theorem fp32OfPat_eq_of_pat (c : HolFloat 23 8) (hs : ¬ c.sign = 1) :
    c = fp32OfPat false (fp32Pat c) := by
  have := fp32OfPat_pat c
  rw [decide_eq_false hs] at this
  exact this.symm

/-- The core of the conformance proof for `0 ≤ x < threshold`. -/
theorem fp32_rte_core {x : Rat} (hx : 0 ≤ x) (hth : x < holFloatThreshold 23 8) :
    let a := fp32OfPat false (fp32Nearest (x * 2 ^ 149))
    fp32RtePred x a ∧
      ∀ c, fp32RtePred x c →
        holFloatIsZero c = holFloatIsZero a ∧ (holFloatIsZero a = false → c = a) := by
  intro a
  have hD := fp32_D_pos
  have hX : 0 ≤ x * 2 ^ 149 := Rat.mul_nonneg hx (Rat.le_of_lt hD)
  have hXth : x * 2 ^ 149 <
      ((fp32N fp32MaxPat : Nat) : Rat) + ((fp32Step fp32MaxPat : Nat) : Rat) / 2 := by
    rw [← fp32_threshold_scaled]; exact Rat.mul_lt_mul_of_pos_right hth hD
  generalize hXd : x * 2 ^ 149 = X at hX hXth
  have hn := fp32Nearest_lt hX hXth
  have hpa : fp32Pat a = fp32Nearest X := by
    show fp32Pat (fp32OfPat false (fp32Nearest (x * 2 ^ 149))) = _
    rw [hXd]; exact fp32Pat_ofPat false (by omega)
  have hsa : ¬ a.sign = 1 := by
    intro h
    have h0 : a.sign = 0 := rfl
    rw [h0] at h; exact absurd h (by decide)
  have hafin : holFloatIsFinite a = true := (fp32_isFinite_iff a).2 (by rw [hpa]; exact hn)
  have hlsba : a.significand.getLsbD 0 = decide (fp32Nearest X % 2 = 1) := by
    show (fp32OfPat false (fp32Nearest (x * 2 ^ 149))).significand.getLsbD 0 = _
    rw [fp32OfPat_lsb, hXd]
  -- scaled distances
  have hdist : ∀ f : HolFloat 23 8, holRatAbs (holFloatToReal f - x) * 2 ^ 149 =
      if f.sign = 1 then ((fp32N (fp32Pat f) : Nat) : Rat) + X else fp32Dist X (fp32Pat f) := by
    intro f; rw [fp32_absdist_scaled f hx, hXd]
  have hda : holRatAbs (holFloatToReal a - x) * 2 ^ 149 = fp32Dist X (fp32Nearest X) := by
    rw [hdist, if_neg hsa, hpa]
  have hle : ∀ b : HolFloat 23 8,
      holRatAbs (holFloatToReal a - x) ≤ holRatAbs (holFloatToReal b - x) := by
    intro b
    apply Rat.le_of_mul_le_mul_right _ hD
    rw [hda, hdist]
    split
    · exact fp32Nearest_le_neg hX _
    · exact fp32Nearest_le hX _
  have hclosest : holIsClosest (fun a => holFloatIsFinite a = true) x a :=
    ⟨hafin, fun b _ => hle b⟩
  -- equal distance to the nearest
  have heq : ∀ c : HolFloat 23 8, holIsClosest (fun a => holFloatIsFinite a = true) x c →
      (c.sign = 1 → fp32Pat c = 0 ∧ fp32Nearest X = 0) ∧
      (¬ c.sign = 1 → fp32Pat c = fp32Nearest X ∨
        (fp32Nearest X % 2 = 0 ∧ fp32Pat c % 2 = 1)) := by
    intro c ⟨_, hc⟩
    have h1 := hc a hafin
    have h2 := hle c
    have hEq : holRatAbs (holFloatToReal c - x) * 2 ^ 149 =
        holRatAbs (holFloatToReal a - x) * 2 ^ 149 := by
      have := Rat.le_antisymm h1 h2; rw [this]
    rw [hda, hdist] at hEq
    constructor
    · intro hs; rw [if_pos hs] at hEq; exact fp32Nearest_eq_neg hX _ hEq
    · intro hs; rw [if_neg hs] at hEq; exact fp32Nearest_eq hX _ hEq
  have hPa : fp32RtePred x a := by
    refine ⟨hclosest, fun b ⟨hb, hbe⟩ => ?_⟩
    rw [hlsba]
    by_cases hn2 : fp32Nearest X % 2 = 0
    · simp [hn2]
    · have ⟨hneg, hpos⟩ := heq b hb
      by_cases hs : b.sign = 1
      · have := (hneg hs).2; omega
      · rcases hpos hs with hbp | ⟨h, _⟩
        · have hba : b = a := by
            rw [fp32OfPat_eq_of_pat b hs, hbp]
            show fp32OfPat false (fp32Nearest X) = fp32OfPat false (fp32Nearest (x * 2 ^ 149))
            rw [hXd]
          rw [hba, hlsba] at hbe; exact hbe
        · exact absurd h hn2
  refine ⟨hPa, fun c ⟨hc, hct⟩ => ?_⟩
  have hcfin : holFloatIsFinite c = true := hc.1
  have hza : holFloatIsZero a = true ↔ fp32Nearest X = 0 := by
    rw [fp32_isZero_iff a hafin, hpa]
  have hzc : holFloatIsZero c = true ↔ fp32Pat c = 0 := fp32_isZero_iff c hcfin
  have ⟨hneg, hpos⟩ := heq c hc
  by_cases hs : c.sign = 1
  · have ⟨hc0, hn0⟩ := hneg hs
    have hzc' : holFloatIsZero c = true := hzc.2 hc0
    have hza' : holFloatIsZero a = true := hza.2 hn0
    refine ⟨by rw [hzc', hza'], fun h => by rw [hza'] at h; exact absurd h (by decide)⟩
  · rcases hpos hs with hcp | ⟨hn2, hc2⟩
    · have hca : c = a := by
        rw [fp32OfPat_eq_of_pat c hs, hcp]
        show fp32OfPat false (fp32Nearest X) = fp32OfPat false (fp32Nearest (x * 2 ^ 149))
        rw [hXd]
      exact ⟨by rw [hca], fun _ => hca⟩
    · exfalso
      have hae : a.significand.getLsbD 0 = false := by rw [hlsba]; simp [hn2]
      have := hct a ⟨hclosest, hae⟩
      rw [fp32OfPat_eq_of_pat c hs, fp32OfPat_lsb] at this
      simp [hc2] at this


section Negate

theorem fp32Pat_negate (f : HolFloat 23 8) : fp32Pat (holFloatNegate f) = fp32Pat f := rfl

theorem holFloatNegate_negate {t w : Nat} [NeZero t] [NeZero w] (f : HolFloat t w) :
    holFloatNegate (holFloatNegate f) = f := by
  unfold holFloatNegate; simp

theorem holFloatToReal_negate (f : HolFloat 23 8) :
    holFloatToReal (holFloatNegate f) = -holFloatToReal f := by
  rw [holFloatToReal_fp32, holFloatToReal_fp32, fp32Pat_negate]
  have hs : ∀ s : BitVec 1, (if ~~~s = 1 then (-1 : Rat) else 1) = -(if s = 1 then -1 else 1) := by
    decide
  show (if ~~~f.sign = 1 then (-1 : Rat) else 1) * _ / _ = _
  rw [hs]
  generalize (2 : Rat) ^ 149 = D
  grind

theorem holFloatIsFinite_negate (f : HolFloat 23 8) :
    holFloatIsFinite (holFloatNegate f) = holFloatIsFinite f := by
  have h1 := fp32_isFinite_iff f
  have h2 := fp32_isFinite_iff (holFloatNegate f)
  rw [fp32Pat_negate] at h2
  rw [Bool.eq_iff_iff, h1, h2]

theorem holRatAbs_neg (y : Rat) : holRatAbs (-y) = holRatAbs y := by
  unfold holRatAbs; split <;> split <;> grind

theorem holIsClosest_negate {x : Rat} {c : HolFloat 23 8}
    (h : holIsClosest (fun a : HolFloat 23 8 => holFloatIsFinite a = true) x c) :
    holIsClosest (fun a : HolFloat 23 8 => holFloatIsFinite a = true) (-x) (holFloatNegate c) := by
  refine ⟨?_, fun b hb => ?_⟩
  · show holFloatIsFinite (holFloatNegate c) = true
    rw [holFloatIsFinite_negate]; exact h.1
  · have hb' : holFloatIsFinite (holFloatNegate b) = true := by
      rw [holFloatIsFinite_negate]; exact hb
    have := h.2 (holFloatNegate b) hb'
    rw [holFloatToReal_negate] at this
    rw [holFloatToReal_negate]
    have e1 : -holFloatToReal c - -x = -(holFloatToReal c - x) := by grind
    have e2 : -holFloatToReal b - x = -(holFloatToReal b - -x) := by grind
    rw [e1, holRatAbs_neg]
    rw [e2, holRatAbs_neg] at this
    exact this

theorem fp32RtePred_negate {x : Rat} {c : HolFloat 23 8} (h : fp32RtePred x c) :
    fp32RtePred (-x) (holFloatNegate c) := by
  refine ⟨holIsClosest_negate h.1, fun b ⟨hb, hbe⟩ => ?_⟩
  have hb' := holIsClosest_negate hb
  rw [Rat.neg_neg] at hb'
  exact h.2 _ ⟨hb', hbe⟩

theorem holFloatIsZero_negate (f : HolFloat 23 8) (hf : holFloatIsFinite f = true) :
    holFloatIsZero (holFloatNegate f) = holFloatIsZero f := by
  have hg : holFloatIsFinite (holFloatNegate f) = true := by rw [holFloatIsFinite_negate]; exact hf
  have h1 := fp32_isZero_iff f hf
  have h2 := fp32_isZero_iff _ hg
  rw [fp32Pat_negate] at h2
  rw [Bool.eq_iff_iff, h1, h2]

end Negate


/-- Computable binary32 `float_round roundTiesToEven toneg x` for a rational
    `x`.  Values at or beyond `threshold` overflow to an infinity.  Otherwise
    the result is the nearest finite float, ties to even, with a zero result's
    sign taken from `toneg`. -/
def holFp32RoundTiesToEven (toneg : Bool) (x : Rat) : HolFloat 23 8 :=
  if x ≤ -holFloatThreshold 23 8 then holFloatMinusInfinity 23 8
  else if x ≥ holFloatThreshold 23 8 then holFloatPlusInfinity 23 8
  else
    let a : HolFloat 23 8 :=
      if x < 0 then holFloatNegate (fp32OfPat false (fp32Nearest (-x * 2 ^ 149)))
      else fp32OfPat false (fp32Nearest (x * 2 ^ 149))
    if holFloatIsZero a then
      (if toneg then holFloatMinusZero 23 8 else holFloatPlusZero 23 8)
    else a

private theorem fp32_zero_select {c a z : HolFloat 23 8}
    (h1 : holFloatIsZero c = holFloatIsZero a) (h2 : holFloatIsZero a = false → c = a) :
    (if holFloatIsZero c then z else c) = (if holFloatIsZero a then z else a) := by
  rw [h1]
  cases ha : holFloatIsZero a
  · rw [h2 ha]
  · rfl

/-- The computable rounding agrees with HOL's choice-based
    `float_round roundTiesToEven` at binary32, for every rational input. -/
theorem holFloatRound_rte_fp32 (toneg : Bool) (x : Rat) :
    (holFloatRound .roundTiesToEven toneg x : HolFloat 23 8) = holFp32RoundTiesToEven toneg x := by
  unfold holFloatRound holRound holFp32RoundTiesToEven
  simp only
  by_cases h1 : x ≤ -holFloatThreshold 23 8
  · rw [if_pos h1, if_pos h1]
    have : holFloatIsZero (holFloatMinusInfinity 23 8) = false := by decide +kernel
    rw [this]; rfl
  rw [if_neg h1, if_neg h1]
  by_cases h2 : x ≥ holFloatThreshold 23 8
  · rw [if_pos h2, if_pos h2]
    have : holFloatIsZero (holFloatPlusInfinity 23 8) = false := by decide +kernel
    rw [this]; rfl
  rw [if_neg h2, if_neg h2]
  have hth : x < holFloatThreshold 23 8 := by grind
  have hth' : -x < holFloatThreshold 23 8 := by grind
  -- the choice meets HOL's predicate once a witness is known
  have hspec : ∀ a : HolFloat 23 8, fp32RtePred x a →
      fp32RtePred x (holClosestSuch (fun a => a.significand.getLsbD 0 = false)
        (fun a => holFloatIsFinite a = true) x) :=
    fun a ha => holClosestSuch_spec _ _ _ ⟨a, ha⟩
  by_cases hneg : x < 0
  · rw [if_pos hneg]
    have hx : 0 ≤ -x := by grind
    obtain ⟨hPa', hall⟩ := fp32_rte_core hx hth'
    generalize fp32OfPat false (fp32Nearest (-x * 2 ^ 149)) = a' at hPa' hall
    have hPa : fp32RtePred x (holFloatNegate a') := by
      have := fp32RtePred_negate hPa'; rwa [Rat.neg_neg] at this
    have hc := hspec _ hPa
    generalize holClosestSuch (t := 23) (w := 8) _ _ x = c at hc ⊢
    have ⟨hz, hne⟩ := hall _ (fp32RtePred_negate hc)
    have hcfin : holFloatIsFinite c = true := hc.1.1
    have ha'fin : holFloatIsFinite a' = true := hPa'.1.1
    rw [holFloatIsZero_negate c hcfin] at hz
    apply fp32_zero_select
    · rw [hz, holFloatIsZero_negate a' ha'fin]
    · intro h
      rw [holFloatIsZero_negate a' ha'fin] at h
      have := hne h
      rw [← this, holFloatNegate_negate]
  · rw [if_neg hneg]
    have hx : 0 ≤ x := by grind
    obtain ⟨hPa, hall⟩ := fp32_rte_core hx hth
    generalize fp32OfPat false (fp32Nearest (x * 2 ^ 149)) = a at hPa hall
    have hc := hspec _ hPa
    generalize holClosestSuch (t := 23) (w := 8) _ _ x = c at hc ⊢
    have ⟨hz, hne⟩ := hall _ hc
    exact fp32_zero_select hz hne

end Flapjack.Binary32Rounding

namespace Flapjack

/-- Flapjack computable binary32 algorithm, exposed for kernel regression replay.
Its original choice specification is preserved by the theorem below. -/
abbrev holFp32RoundTiesToEven := Binary32Rounding.holFp32RoundTiesToEven

/-- Agreement with the full rational choice specification at binary32, for
all inputs and requested zero signs. Flapjack infrastructure with no separately
named original HOL theorem; no extra finite or successful-result premise. -/
theorem holFloatRound_rte_fp32 (toneg : Bool) (x : Rat) :
    (holFloatRound .roundTiesToEven toneg x : HolFloat 23 8) =
      holFp32RoundTiesToEven toneg x :=
  Binary32Rounding.holFloatRound_rte_fp32 toneg x

end Flapjack
