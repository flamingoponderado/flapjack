import Flapjack.Misc.BinaryIeeeRound

/-!
# Computable binary64 round-to-nearest-even, proved equal to HOL `float_round`

HOL specifies `round roundTiesToEven` through the Hilbert choice
`closest_such` (`HOL/src/floating-point/binary_ieeeScript.sml:347-443`),
rendered noncomputably in `Flapjack.Misc.BinaryIeeeRound`.  This module (bead
`flapjack-h29l.6.2.3`) gives a computable integer/`Rat` algorithm for binary64
(`t = 52`, `w = 11`) and the kernel-checked theorem
`holFloatRound_rte_fp64`: for every rational `x` and zero-sign flag `toneg`,
`float_round roundTiesToEven toneg x` equals `holFp64RoundTiesToEven toneg x`.

The proof works in units of `2^-1074`:
* A finite binary64 float with 63-bit pattern `q` (exponent and significand)
  has value `±fp64N q / 2^1074`, where `fp64N q` is `q` in the subnormal range
  and `(2^52 + q mod 2^52) * 2^(q / 2^52 - 1)` otherwise
  (`holFloatToReal_fp64`).
* `fp64N` is strictly increasing with successor gap `fp64Step`
  (`fp64N_succ`), so the patterns bracketing `X = |x| * 2^1074` are
  `fp64Bracket ⌊X⌋` and its successor (`fp64Bracket_spec`).
* `fp64Nearest` picks the nearer of the two, ties to the even pattern.  It is
  at least as close as every finite float of either sign (`fp64Nearest_le`,
  `fp64Nearest_le_neg`).  An equally close float is the same float, the odd
  partner at a tie, or `-0` when the nearest is `+0` (`fp64Nearest_eq`,
  `fp64Nearest_eq_neg`).
* Hence the computed float satisfies HOL's choice predicate.  Every float
  satisfying it is the computed one, or both are zeros, whose sign
  `float_round` then fixes (`fp64_rte_core`).  Negative inputs follow by
  `float_negate` symmetry.

HOL standard library, so untagged.
-/

namespace Flapjack

/-- The 63-bit pattern `exponent * 2^52 + significand` of a binary64 float. -/
def fp64Pat (f : HolFloat 52 11) : Nat := f.exponent.toNat * 2 ^ 52 + f.significand.toNat

/-- The magnitude of pattern `q` in units of `2^-1074`. -/
def fp64N (q : Nat) : Nat := if q < 2 ^ 52 then q else (2 ^ 52 + q % 2 ^ 52) * 2 ^ (q / 2 ^ 52 - 1)

theorem fp64Pat_div (f : HolFloat 52 11) : fp64Pat f / 2 ^ 52 = f.exponent.toNat := by
  have := f.significand.isLt
  unfold fp64Pat; omega

theorem fp64Pat_mod (f : HolFloat 52 11) : fp64Pat f % 2 ^ 52 = f.significand.toNat := by
  have := f.significand.isLt
  unfold fp64Pat; omega

/-- A binary64 float's value is `±fp64N (pattern) / 2^1074`. -/
theorem holFloatToReal_fp64 (f : HolFloat 52 11) :
    holFloatToReal f = (if f.sign = 1 then -1 else 1) * ((fp64N (fp64Pat f) : Nat) : Rat) / 2 ^ 1074 := by
  have hs : f.significand.toNat < 2 ^ 52 := f.significand.isLt
  have hsign : (-1 : Rat) ^ f.sign.toNat = (if f.sign = 1 then -1 else 1) := by
    have : f.sign = 0 ∨ f.sign = 1 := by
      have h := f.sign.isLt
      rcases Nat.lt_succ_iff.mp h |> Nat.le_one_iff_eq_zero_or_eq_one.mp with h0 | h1
      · left; exact BitVec.eq_of_toNat_eq (by simp [h0])
      · right; exact BitVec.eq_of_toNat_eq (by simp [h1])
    rcases this with h | h <;> rw [h] <;> decide
  unfold holFloatToReal fp64N
  rw [hsign]
  by_cases he : f.exponent = 0
  · have he' : f.exponent.toNat = 0 := by simp [he]
    have hlt : fp64Pat f < 2 ^ 52 := by unfold fp64Pat; omega
    have hp : fp64Pat f = f.significand.toNat := by unfold fp64Pat; omega
    simp only [he, if_true, hp, holFloatBias]
    grind
  · have hne : f.exponent.toNat ≠ 0 := fun h => he (BitVec.eq_of_toNat_eq (by simpa using h))
    have hge : ¬ fp64Pat f < 2 ^ 52 := by unfold fp64Pat; have := Nat.pos_of_ne_zero hne; omega
    simp only [he, if_false, hge, fp64Pat_div, fp64Pat_mod, holFloatBias]
    obtain ⟨k, hk⟩ : ∃ k, f.exponent.toNat = k + 1 := ⟨f.exponent.toNat - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    push_cast
    grind

/-- The gap from pattern `q` to pattern `q + 1`. -/
def fp64Step (q : Nat) : Nat := if q < 2 ^ 52 then 1 else 2 ^ (q / 2 ^ 52 - 1)

theorem fp64Step_pos (q : Nat) : 0 < fp64Step q := by
  unfold fp64Step; split
  · decide
  · exact Nat.two_pow_pos _

/-- Division and remainder of `e * M + s` by `M` when `s < M`. -/
theorem fp64_divmod {M e s : Nat} (hs : s < M) : (e * M + s) / M = e ∧ (e * M + s) % M = s := by
  have hM : 0 < M := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hs, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

theorem fp64N_succ (q : Nat) : fp64N (q + 1) = fp64N q + fp64Step q := by
  unfold fp64N fp64Step
  generalize hM : (2 : Nat) ^ 52 = M
  have hMpos : 2 ≤ M := by rw [← hM]; decide
  by_cases h1 : q + 1 < M
  · have h0 : q < M := by omega
    simp [h1, h0]
  · by_cases h0 : q < M
    · have hq : q + 1 = 1 * M + 0 := by omega
      have ⟨hd, hm⟩ := fp64_divmod (e := 1) (show 0 < M by omega)
      rw [if_neg h1, if_pos h0, if_pos h0, hq, hd, hm]
      omega
    · simp only [h1, h0, if_false]
      obtain ⟨e, s, hs, rfl⟩ : ∃ e s, s < M ∧ q = e * M + s :=
        ⟨q / M, q % M, Nat.mod_lt _ (by omega), (Nat.div_add_mod' q M).symm⟩
      have ⟨hd, hm⟩ := fp64_divmod (e := e) hs
      have he : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with h | h
        · subst h; simp at h0; omega
        · exact h
      rw [hd, hm]
      by_cases hs1 : s + 1 < M
      · have ⟨hd', hm'⟩ := fp64_divmod (e := e) hs1
        rw [Nat.add_assoc, hd', hm', Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.one_mul]
        omega
      · have hs' : s + 1 = M := by omega
        have hq : e * M + s + 1 = (e + 1) * M + 0 := by rw [Nat.add_mul]; omega
        have ⟨hd', hm'⟩ := fp64_divmod (e := e + 1) (show 0 < M by omega)
        rw [hq, hd', hm']
        obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
        simp only [Nat.add_sub_cancel, Nat.pow_succ, Nat.add_zero]
        have hsM : M + s + 1 = 2 * M := by omega
        calc M * (2 ^ k * 2) = 2 * M * 2 ^ k := by
                rw [Nat.mul_comm 2 M, Nat.mul_assoc, Nat.mul_comm 2]
          _ = (M + s + 1) * 2 ^ k := by rw [hsM]
          _ = (M + s) * 2 ^ k + 2 ^ k := by rw [Nat.add_mul (M + s) 1, Nat.one_mul]

theorem fp64N_mono {q r : Nat} (h : q ≤ r) : fp64N q ≤ fp64N r := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [fp64N_succ]; omega

theorem fp64N_strictMono {q r : Nat} (h : q < r) : fp64N q < fp64N r := by
  have h1 := fp64N_succ q
  have h2 := fp64Step_pos q
  have h3 := fp64N_mono (show q + 1 ≤ r from h)
  omega


/-- The largest pattern whose value `N` is at most `k`: `k` itself in the
    subnormal range, otherwise exponent `log2 k - 51` and the top 53 bits of
    `k`. -/
def fp64Bracket (k : Nat) : Nat :=
  if k < 2 ^ 52 then k
  else (k.log2 - 51) * 2 ^ 52 + (k / 2 ^ (k.log2 - 52) - 2 ^ 52)

theorem fp64Bracket_spec (k : Nat) :
    fp64N (fp64Bracket k) ≤ k ∧ k < fp64N (fp64Bracket k + 1) := by
  rw [fp64N_succ]
  unfold fp64Bracket
  by_cases hk : k < 2 ^ 52
  · rw [if_pos hk]
    unfold fp64N fp64Step
    rw [if_pos hk, if_pos hk]
    omega
  · rw [if_neg hk]
    have hk0 : k ≠ 0 := by intro h; subst h; exact hk (by decide)
    have hL : 52 ≤ k.log2 := (Nat.le_log2 hk0).2 (by omega)
    obtain ⟨j, hj⟩ : ∃ j, k.log2 = 52 + j := ⟨k.log2 - 52, by omega⟩
    have hlo : 2 ^ (52 + j) ≤ k := hj ▸ Nat.log2_self_le hk0
    have hhi : k < 2 ^ (52 + j + 1) := hj ▸ Nat.lt_log2_self
    have hlo2 : 2 ^ 52 * 2 ^ j ≤ k := by rw [← Nat.pow_add]; exact hlo
    have hhi2 : k < 2 ^ 53 * 2 ^ j := by
      rw [← Nat.pow_add, show 53 + j = 52 + j + 1 by omega]; exact hhi
    rw [hj, show 52 + j - 51 = j + 1 by omega, show 52 + j - 52 = j by omega]
    clear hlo hhi
    generalize hS : (2 : Nat) ^ j = S at *
    have hSpos : 0 < S := by rw [← hS]; exact Nat.two_pow_pos _
    have hlo' : 2 ^ 52 * S ≤ k := hlo2
    have hhi' : k < 2 ^ 53 * S := hhi2
    have hm1 : 2 ^ 52 ≤ k / S := (Nat.le_div_iff_mul_le hSpos).2 (by rw [Nat.mul_comm] at hlo'; omega)
    have hm2 : k / S < 2 ^ 53 := (Nat.div_lt_iff_lt_mul hSpos).2 (by rw [Nat.mul_comm] at hhi'; omega)
    have hsig : k / S - 2 ^ 52 < 2 ^ 52 := by omega
    have ⟨hd, hm⟩ := fp64_divmod (e := j + 1) hsig
    have hge : ¬ (j + 1) * 2 ^ 52 + (k / S - 2 ^ 52) < 2 ^ 52 := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    unfold fp64N fp64Step
    rw [if_neg hge, if_neg hge, hd, hm, Nat.add_sub_cancel, hS,
      show 2 ^ 52 + (k / S - 2 ^ 52) = k / S by omega]
    refine ⟨Nat.div_mul_le_self k S, ?_⟩
    have := Nat.lt_mul_div_succ k hSpos
    rw [Nat.mul_comm S, Nat.add_mul, Nat.one_mul] at this
    exact this


/-- The binary64 float with the given sign and 63-bit pattern. -/
def fp64OfPat (neg : Bool) (q : Nat) : HolFloat 52 11 :=
  { sign := if neg then 1 else 0, exponent := BitVec.ofNat 11 (q / 2 ^ 52),
    significand := BitVec.ofNat 52 (q % 2 ^ 52) }

theorem fp64Pat_lt (f : HolFloat 52 11) : fp64Pat f < 2 ^ 63 := by
  have h1 := f.exponent.isLt
  have h2 := f.significand.isLt
  unfold fp64Pat
  have : f.exponent.toNat * 2 ^ 52 ≤ (2 ^ 11 - 1) * 2 ^ 52 := Nat.mul_le_mul_right _ (by omega)
  omega

theorem fp64Pat_ofPat (neg : Bool) {q : Nat} (hq : q < 2 ^ 63) : fp64Pat (fp64OfPat neg q) = q := by
  unfold fp64Pat fp64OfPat
  have hd : q / 2 ^ 52 < 2 ^ 11 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd, Nat.mod_mod]
  exact Nat.div_add_mod' q (2 ^ 52)

theorem fp64OfPat_pat (f : HolFloat 52 11) : fp64OfPat (decide (f.sign = 1)) (fp64Pat f) = f := by
  obtain ⟨s, e, m⟩ := f
  have hsig : fp64OfPat (decide (s = 1)) (fp64Pat ⟨s, e, m⟩) =
      ⟨if decide (s = 1) then 1 else 0, BitVec.ofNat 11 e.toNat, BitVec.ofNat 52 m.toNat⟩ := by
    unfold fp64OfPat
    rw [fp64Pat_div, fp64Pat_mod]
  rw [hsig]
  have hs : ∀ s : BitVec 1, (if decide (s = 1) = true then (1 : BitVec 1) else 0) = s := by decide
  rw [hs s]
  simp

theorem fp64_isFinite_iff (f : HolFloat 52 11) :
    holFloatIsFinite f = true ↔ fp64Pat f < 2047 * 2 ^ 52 := by
  have h1 := f.exponent.isLt
  have h2 := f.significand.isLt
  have hne : f.exponent ≠ BitVec.allOnes 11 ↔ f.exponent.toNat ≠ 2047 := by
    constructor
    · intro h h'; exact h (BitVec.eq_of_toNat_eq (by simp [h']))
    · intro h h'; exact h (by simp [h'])
  have hfin : holFloatIsFinite f = true ↔ f.exponent ≠ BitVec.allOnes 11 := by
    unfold holFloatIsFinite holFloatValue
    by_cases he : f.exponent = BitVec.allOnes 11
    · rw [if_pos he]
      by_cases hs : f.significand = 0
      · rw [if_pos hs]; simp [he]
      · rw [if_neg hs]; simp [he]
    · rw [if_neg he]
      simpa using he
  rw [hfin, hne]
  unfold fp64Pat
  constructor
  · intro h
    have : f.exponent.toNat ≤ 2046 := by omega
    have : f.exponent.toNat * 2 ^ 52 ≤ 2046 * 2 ^ 52 := Nat.mul_le_mul_right _ this
    omega
  · intro h h'
    rw [h'] at h
    omega

theorem fp64OfPat_lsb (neg : Bool) (q : Nat) :
    (fp64OfPat neg q).significand.getLsbD 0 = decide (q % 2 = 1) := by
  unfold fp64OfPat
  simp only [BitVec.getLsbD_ofNat, Nat.testBit_zero]
  have : q % 2 ^ 52 % 2 = q % 2 := Nat.mod_mod_of_dvd q (by decide)
  simp [this]

theorem fp64N_eq_zero {q : Nat} : fp64N q = 0 ↔ q = 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · exact h0
    · have := fp64N_strictMono h0
      have h00 : fp64N 0 = 0 := by decide
      omega
  · intro h; subst h; decide


/-- The pattern nearest to `X ≥ 0` (in units of `2^-1074`), ties to the even
    pattern, among the two patterns bracketing `X`. -/
def fp64Nearest (X : Rat) : Nat :=
  let p := fp64Bracket X.floor.toNat
  let lo : Rat := (fp64N p : Rat)
  let hi : Rat := (fp64N (p + 1) : Rat)
  if X - lo < hi - X then p
  else if hi - X < X - lo then p + 1
  else if p % 2 = 0 then p else p + 1

theorem fp64Bracket_rat {X : Rat} (hX : 0 ≤ X) :
    ((fp64N (fp64Bracket X.floor.toNat) : Nat) : Rat) ≤ X ∧
      X < ((fp64N (fp64Bracket X.floor.toNat + 1) : Nat) : Rat) := by
  have ⟨h1, h2⟩ := fp64Bracket_spec X.floor.toNat
  have hfl : 0 ≤ X.floor := Rat.le_floor_iff.2 (by simpa using hX)
  have hk : ((X.floor.toNat : Nat) : Rat) = (X.floor : Rat) := by
    have h := congrArg (fun z : Int => (z : Rat)) (Int.toNat_of_nonneg hfl)
    rw [← h]
    exact (Rat.intCast_natCast _).symm
  have hle := Rat.floor_le X
  have hlt := Rat.lt_floor_add_one X
  have c1 : ((fp64N (fp64Bracket X.floor.toNat) : Nat) : Rat) ≤ ((X.floor.toNat : Nat) : Rat) := by
    exact_mod_cast h1
  have c2 : ((X.floor.toNat : Nat) : Rat) + 1 ≤ ((fp64N (fp64Bracket X.floor.toNat + 1) : Nat) : Rat) := by
    exact_mod_cast h2
  push_cast at hlt
  constructor <;> grind


section Nearest

variable {X : Rat}

/-- Distance, in units of `2^-1074`, from `X` to the value of pattern `q`. -/
def fp64Dist (X : Rat) (q : Nat) : Rat := holRatAbs (((fp64N q : Nat) : Rat) - X)

theorem fp64Nearest_cases (hX : 0 ≤ X) :
    (fp64Nearest X = fp64Bracket X.floor.toNat ∨ fp64Nearest X = fp64Bracket X.floor.toNat + 1) ∧
      fp64Dist X (fp64Nearest X) ≤ X - ((fp64N (fp64Bracket X.floor.toNat) : Nat) : Rat) ∧
      fp64Dist X (fp64Nearest X) ≤ ((fp64N (fp64Bracket X.floor.toNat + 1) : Nat) : Rat) - X ∧
      (X - ((fp64N (fp64Bracket X.floor.toNat) : Nat) : Rat) =
          ((fp64N (fp64Bracket X.floor.toNat + 1) : Nat) : Rat) - X → fp64Nearest X % 2 = 0) := by
  have ⟨h1, h2⟩ := fp64Bracket_rat hX
  unfold fp64Nearest fp64Dist holRatAbs
  simp only
  generalize fp64Bracket X.floor.toNat = p at *
  generalize hlo : ((fp64N p : Nat) : Rat) = lo at *
  generalize hhi : ((fp64N (p + 1) : Nat) : Rat) = hi at *
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

theorem fp64Nearest_succ_le (_hX : 0 ≤ X)
    (h : fp64Nearest X = fp64Bracket X.floor.toNat + 1) :
    ((fp64N (fp64Bracket X.floor.toNat + 1) : Nat) : Rat) - X ≤
      X - ((fp64N (fp64Bracket X.floor.toNat) : Nat) : Rat) := by
  revert h
  unfold fp64Nearest
  simp only
  generalize fp64Bracket X.floor.toNat = p
  generalize ((fp64N p : Nat) : Rat) = lo
  generalize ((fp64N (p + 1) : Nat) : Rat) = hi
  intro h
  by_cases c1 : X - lo < hi - X
  · rw [if_pos c1] at h; omega
  · grind

private theorem fp64Dist_of_le {q : Nat} (h : ((fp64N q : Nat) : Rat) ≤ X) :
    fp64Dist X q = X - ((fp64N q : Nat) : Rat) := by
  unfold fp64Dist holRatAbs; split <;> grind

private theorem fp64Dist_of_ge {q : Nat} (h : X ≤ ((fp64N q : Nat) : Rat)) :
    fp64Dist X q = ((fp64N q : Nat) : Rat) - X := by
  unfold fp64Dist holRatAbs; split <;> grind

private theorem fp64N_cast_le {q r : Nat} (h : q ≤ r) :
    ((fp64N q : Nat) : Rat) ≤ ((fp64N r : Nat) : Rat) := by exact_mod_cast fp64N_mono h

private theorem fp64N_cast_lt {q r : Nat} (h : q < r) :
    ((fp64N q : Nat) : Rat) < ((fp64N r : Nat) : Rat) := by exact_mod_cast fp64N_strictMono h

/-- The nearest pattern is at least as close to `X` as every pattern. -/
theorem fp64Nearest_le (hX : 0 ≤ X) (q : Nat) :
    fp64Dist X (fp64Nearest X) ≤ fp64Dist X q := by
  have ⟨_, hlo, hhi, _⟩ := fp64Nearest_cases hX
  have ⟨h1, h2⟩ := fp64Bracket_rat hX
  generalize fp64Bracket X.floor.toNat = p at *
  by_cases hq : q ≤ p
  · have := fp64N_cast_le hq
    rw [fp64Dist_of_le (q := q) (by grind)]; grind
  · have := fp64N_cast_le (show p + 1 ≤ q by omega)
    rw [fp64Dist_of_ge (q := q) (by grind)]; grind

/-- No value of the opposite sign is closer than the nearest pattern. -/
theorem fp64Nearest_le_neg (hX : 0 ≤ X) (q : Nat) :
    fp64Dist X (fp64Nearest X) ≤ ((fp64N q : Nat) : Rat) + X := by
  have ⟨_, hlo, _, _⟩ := fp64Nearest_cases hX
  have h0 : (0 : Rat) ≤ ((fp64N (fp64Bracket X.floor.toNat) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  have h1 : (0 : Rat) ≤ ((fp64N q : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  grind

/-- A pattern as close as the nearest one is the nearest one, or the odd
    partner of an even nearest pattern at a tie. -/
theorem fp64Nearest_eq (hX : 0 ≤ X) (q : Nat)
    (h : fp64Dist X q = fp64Dist X (fp64Nearest X)) :
    q = fp64Nearest X ∨ (fp64Nearest X % 2 = 0 ∧ q % 2 = 1) := by
  have ⟨hcase, hlo, hhi, htie⟩ := fp64Nearest_cases hX
  have ⟨h1, h2⟩ := fp64Bracket_rat hX
  generalize fp64Nearest X = a at *
  generalize fp64Bracket X.floor.toNat = p at *
  have hp : fp64Dist X p = X - ((fp64N p : Nat) : Rat) := fp64Dist_of_le h1
  have hp1 : fp64Dist X (p + 1) = ((fp64N (p + 1) : Nat) : Rat) - X := fp64Dist_of_ge (by grind)
  by_cases hlt : q < p
  · have := fp64N_cast_lt hlt
    rw [fp64Dist_of_le (q := q) (by grind)] at h; exfalso; grind
  by_cases hgt : p + 1 < q
  · have := fp64N_cast_lt hgt
    rw [fp64Dist_of_ge (q := q) (by grind)] at h; exfalso; grind
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
theorem fp64Nearest_eq_neg (hX : 0 ≤ X) (q : Nat)
    (h : ((fp64N q : Nat) : Rat) + X = fp64Dist X (fp64Nearest X)) :
    q = 0 ∧ fp64Nearest X = 0 := by
  have ⟨_, hlo, _, _⟩ := fp64Nearest_cases hX
  have h0 : (0 : Rat) ≤ ((fp64N (fp64Bracket X.floor.toNat) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  have h1 : (0 : Rat) ≤ ((fp64N q : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  have hq0 : ((fp64N q : Nat) : Rat) = 0 := by grind
  have hp0 : ((fp64N (fp64Bracket X.floor.toNat) : Nat) : Rat) = 0 := by grind
  have hq : q = 0 := fp64N_eq_zero.1 (by exact_mod_cast hq0)
  have hp : fp64Bracket X.floor.toNat = 0 := fp64N_eq_zero.1 (by exact_mod_cast hp0)
  refine ⟨hq, ?_⟩
  have hdp : fp64Dist X (fp64Bracket X.floor.toNat) = fp64Dist X (fp64Nearest X) := by
    rw [fp64Dist_of_le (q := fp64Bracket X.floor.toNat) (by grind)]; grind
  rcases fp64Nearest_eq hX _ hdp with h' | ⟨_, h'⟩
  · rw [← h', hp]
  · rw [hp] at h'; omega

end Nearest


/-- The largest finite binary64 pattern. -/
def fp64MaxPat : Nat := 2047 * 2 ^ 52 - 1

/-- `threshold` in units of `2^-1074`: the largest finite value plus half its gap. -/
theorem fp64_threshold_scaled :
    holFloatThreshold 52 11 * 2 ^ 1074 =
      ((fp64N fp64MaxPat : Nat) : Rat) + ((fp64Step fp64MaxPat : Nat) : Rat) / 2 := by
  decide +kernel

theorem fp64Nearest_lt {X : Rat} (hX : 0 ≤ X)
    (hth : X < ((fp64N fp64MaxPat : Nat) : Rat) + ((fp64Step fp64MaxPat : Nat) : Rat) / 2) :
    fp64Nearest X < 2047 * 2 ^ 52 := by
  have ⟨hcase, _, _, _⟩ := fp64Nearest_cases hX
  have ⟨h1, h2⟩ := fp64Bracket_rat hX
  have hsucc : ((fp64N (fp64MaxPat + 1) : Nat) : Rat) =
      ((fp64N fp64MaxPat : Nat) : Rat) + ((fp64Step fp64MaxPat : Nat) : Rat) := by
    rw [fp64N_succ]; push_cast; rfl
  have hstep : (0 : Rat) < ((fp64Step fp64MaxPat : Nat) : Rat) := by exact_mod_cast fp64Step_pos _
  have hp : fp64Bracket X.floor.toNat ≤ fp64MaxPat := by
    apply Nat.le_of_not_lt; intro hlt
    have := fp64N_cast_le (show fp64MaxPat + 1 ≤ fp64Bracket X.floor.toNat by omega)
    grind
  have hmax : fp64MaxPat + 1 = 2047 * 2 ^ 52 := by decide
  rcases hcase with h | h
  · rw [h]; omega
  · by_cases hpm : fp64Bracket X.floor.toNat = fp64MaxPat
    · have := fp64Nearest_succ_le hX h
      rw [hpm] at this h1 h2
      exfalso; grind
    · rw [h]; omega

/-- `2^1074` is positive in `Rat`. -/
theorem fp64_D_pos : (0 : Rat) < 2 ^ 1074 := Rat.pow_pos (by decide)

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

/-- The distance from `x ≥ 0` to a binary64 float, scaled by `2^1074`. -/
theorem fp64_absdist_scaled (f : HolFloat 52 11) {x : Rat} (hx : 0 ≤ x) :
    holRatAbs (holFloatToReal f - x) * 2 ^ 1074 =
      if f.sign = 1 then ((fp64N (fp64Pat f) : Nat) : Rat) + x * 2 ^ 1074
      else fp64Dist (x * 2 ^ 1074) (fp64Pat f) := by
  have hD : (0 : Rat) < 2 ^ 1074 := fp64_D_pos
  rw [holRatAbs_mul_pos _ _ hD, holFloatToReal_fp64]
  have hN : (0 : Rat) ≤ ((fp64N (fp64Pat f) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  unfold fp64Dist
  by_cases hs : f.sign = 1
  · rw [if_pos hs, if_pos hs]
    have hx' : 0 ≤ x * 2 ^ 1074 := Rat.mul_nonneg hx (Rat.le_of_lt hD)
    unfold holRatAbs
    generalize (2 : Rat) ^ 1074 = D at *
    have : (-1 * ((fp64N (fp64Pat f) : Nat) : Rat) / D - x) * D =
        -(((fp64N (fp64Pat f) : Nat) : Rat) + x * D) := by grind
    rw [this]; split <;> grind
  · rw [if_neg hs, if_neg hs]
    generalize (2 : Rat) ^ 1074 = D at *
    congr 1
    grind

/-- A finite binary64 float is zero exactly when its pattern is zero. -/
theorem fp64_isZero_iff (f : HolFloat 52 11) (hf : holFloatIsFinite f = true) :
    holFloatIsZero f = true ↔ fp64Pat f = 0 := by
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
    rw [← hr, holFloatToReal_fp64, ← fp64N_eq_zero]
    have hD : (0 : Rat) < 2 ^ 1074 := fp64_D_pos
    constructor
    · intro h
      have : ((fp64N (fp64Pat f) : Nat) : Rat) = 0 := by
        by_cases hs : f.sign = 1 <;> simp [hs] at h <;> grind
      exact_mod_cast this
    · intro h; rw [h]; generalize (2 : Rat) ^ 1074 = D; simp [Rat.div_def]


/-- HOL's `round roundTiesToEven` choice predicate at `x`: a closest finite
    float, preferring an even significand among the closest. -/
def fp64RtePred (x : Rat) (c : HolFloat 52 11) : Prop :=
  holIsClosest (fun a : HolFloat 52 11 => holFloatIsFinite a = true) x c ∧
    ∀ b : HolFloat 52 11, holIsClosest (fun a : HolFloat 52 11 => holFloatIsFinite a = true) x b ∧
      b.significand.getLsbD 0 = false → c.significand.getLsbD 0 = false

theorem fp64OfPat_sign_false (q : Nat) : (fp64OfPat false q).sign = 0 := rfl

theorem fp64OfPat_eq_of_pat (c : HolFloat 52 11) (hs : ¬ c.sign = 1) :
    c = fp64OfPat false (fp64Pat c) := by
  have := fp64OfPat_pat c
  rw [decide_eq_false hs] at this
  exact this.symm

/-- The core of the conformance proof for `0 ≤ x < threshold`. -/
theorem fp64_rte_core {x : Rat} (hx : 0 ≤ x) (hth : x < holFloatThreshold 52 11) :
    let a := fp64OfPat false (fp64Nearest (x * 2 ^ 1074))
    fp64RtePred x a ∧
      ∀ c, fp64RtePred x c →
        holFloatIsZero c = holFloatIsZero a ∧ (holFloatIsZero a = false → c = a) := by
  intro a
  have hD := fp64_D_pos
  have hX : 0 ≤ x * 2 ^ 1074 := Rat.mul_nonneg hx (Rat.le_of_lt hD)
  have hXth : x * 2 ^ 1074 <
      ((fp64N fp64MaxPat : Nat) : Rat) + ((fp64Step fp64MaxPat : Nat) : Rat) / 2 := by
    rw [← fp64_threshold_scaled]; exact Rat.mul_lt_mul_of_pos_right hth hD
  generalize hXd : x * 2 ^ 1074 = X at hX hXth
  have hn := fp64Nearest_lt hX hXth
  have hpa : fp64Pat a = fp64Nearest X := by
    show fp64Pat (fp64OfPat false (fp64Nearest (x * 2 ^ 1074))) = _
    rw [hXd]; exact fp64Pat_ofPat false (by omega)
  have hsa : ¬ a.sign = 1 := by
    intro h
    have h0 : a.sign = 0 := rfl
    rw [h0] at h; exact absurd h (by decide)
  have hafin : holFloatIsFinite a = true := (fp64_isFinite_iff a).2 (by rw [hpa]; exact hn)
  have hlsba : a.significand.getLsbD 0 = decide (fp64Nearest X % 2 = 1) := by
    show (fp64OfPat false (fp64Nearest (x * 2 ^ 1074))).significand.getLsbD 0 = _
    rw [fp64OfPat_lsb, hXd]
  -- scaled distances
  have hdist : ∀ f : HolFloat 52 11, holRatAbs (holFloatToReal f - x) * 2 ^ 1074 =
      if f.sign = 1 then ((fp64N (fp64Pat f) : Nat) : Rat) + X else fp64Dist X (fp64Pat f) := by
    intro f; rw [fp64_absdist_scaled f hx, hXd]
  have hda : holRatAbs (holFloatToReal a - x) * 2 ^ 1074 = fp64Dist X (fp64Nearest X) := by
    rw [hdist, if_neg hsa, hpa]
  have hle : ∀ b : HolFloat 52 11,
      holRatAbs (holFloatToReal a - x) ≤ holRatAbs (holFloatToReal b - x) := by
    intro b
    apply Rat.le_of_mul_le_mul_right _ hD
    rw [hda, hdist]
    split
    · exact fp64Nearest_le_neg hX _
    · exact fp64Nearest_le hX _
  have hclosest : holIsClosest (fun a => holFloatIsFinite a = true) x a :=
    ⟨hafin, fun b _ => hle b⟩
  -- equal distance to the nearest
  have heq : ∀ c : HolFloat 52 11, holIsClosest (fun a => holFloatIsFinite a = true) x c →
      (c.sign = 1 → fp64Pat c = 0 ∧ fp64Nearest X = 0) ∧
      (¬ c.sign = 1 → fp64Pat c = fp64Nearest X ∨
        (fp64Nearest X % 2 = 0 ∧ fp64Pat c % 2 = 1)) := by
    intro c ⟨_, hc⟩
    have h1 := hc a hafin
    have h2 := hle c
    have hEq : holRatAbs (holFloatToReal c - x) * 2 ^ 1074 =
        holRatAbs (holFloatToReal a - x) * 2 ^ 1074 := by
      have := Rat.le_antisymm h1 h2; rw [this]
    rw [hda, hdist] at hEq
    constructor
    · intro hs; rw [if_pos hs] at hEq; exact fp64Nearest_eq_neg hX _ hEq
    · intro hs; rw [if_neg hs] at hEq; exact fp64Nearest_eq hX _ hEq
  have hPa : fp64RtePred x a := by
    refine ⟨hclosest, fun b ⟨hb, hbe⟩ => ?_⟩
    rw [hlsba]
    by_cases hn2 : fp64Nearest X % 2 = 0
    · simp [hn2]
    · have ⟨hneg, hpos⟩ := heq b hb
      by_cases hs : b.sign = 1
      · have := (hneg hs).2; omega
      · rcases hpos hs with hbp | ⟨h, _⟩
        · have hba : b = a := by
            rw [fp64OfPat_eq_of_pat b hs, hbp]
            show fp64OfPat false (fp64Nearest X) = fp64OfPat false (fp64Nearest (x * 2 ^ 1074))
            rw [hXd]
          rw [hba, hlsba] at hbe; exact hbe
        · exact absurd h hn2
  refine ⟨hPa, fun c ⟨hc, hct⟩ => ?_⟩
  have hcfin : holFloatIsFinite c = true := hc.1
  have hza : holFloatIsZero a = true ↔ fp64Nearest X = 0 := by
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
        show fp64OfPat false (fp64Nearest X) = fp64OfPat false (fp64Nearest (x * 2 ^ 1074))
        rw [hXd]
      exact ⟨by rw [hca], fun _ => hca⟩
    · exfalso
      have hae : a.significand.getLsbD 0 = false := by rw [hlsba]; simp [hn2]
      have := hct a ⟨hclosest, hae⟩
      rw [fp64OfPat_eq_of_pat c hs, fp64OfPat_lsb] at this
      simp [hc2] at this


section Negate

theorem fp64Pat_negate (f : HolFloat 52 11) : fp64Pat (holFloatNegate f) = fp64Pat f := rfl

theorem holFloatNegate_negate {t : Nat} {w : Nat} [NeZero t] [NeZero w] (f : HolFloat t w) :
    holFloatNegate (holFloatNegate f) = f := by
  unfold holFloatNegate; simp

theorem holFloatToReal_negate (f : HolFloat 52 11) :
    holFloatToReal (holFloatNegate f) = -holFloatToReal f := by
  rw [holFloatToReal_fp64, holFloatToReal_fp64, fp64Pat_negate]
  have hs : ∀ s : BitVec 1, (if ~~~s = 1 then (-1 : Rat) else 1) = -(if s = 1 then -1 else 1) := by
    decide
  show (if ~~~f.sign = 1 then (-1 : Rat) else 1) * _ / _ = _
  rw [hs]
  generalize (2 : Rat) ^ 1074 = D
  grind

theorem holFloatIsFinite_negate (f : HolFloat 52 11) :
    holFloatIsFinite (holFloatNegate f) = holFloatIsFinite f := by
  have h1 := fp64_isFinite_iff f
  have h2 := fp64_isFinite_iff (holFloatNegate f)
  rw [fp64Pat_negate] at h2
  rw [Bool.eq_iff_iff, h1, h2]

theorem holRatAbs_neg (y : Rat) : holRatAbs (-y) = holRatAbs y := by
  unfold holRatAbs; split <;> split <;> grind

theorem holIsClosest_negate {x : Rat} {c : HolFloat 52 11}
    (h : holIsClosest (fun a : HolFloat 52 11 => holFloatIsFinite a = true) x c) :
    holIsClosest (fun a : HolFloat 52 11 => holFloatIsFinite a = true) (-x) (holFloatNegate c) := by
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

theorem fp64RtePred_negate {x : Rat} {c : HolFloat 52 11} (h : fp64RtePred x c) :
    fp64RtePred (-x) (holFloatNegate c) := by
  refine ⟨holIsClosest_negate h.1, fun b ⟨hb, hbe⟩ => ?_⟩
  have hb' := holIsClosest_negate hb
  rw [Rat.neg_neg] at hb'
  exact h.2 _ ⟨hb', hbe⟩

theorem holFloatIsZero_negate (f : HolFloat 52 11) (hf : holFloatIsFinite f = true) :
    holFloatIsZero (holFloatNegate f) = holFloatIsZero f := by
  have hg : holFloatIsFinite (holFloatNegate f) = true := by rw [holFloatIsFinite_negate]; exact hf
  have h1 := fp64_isZero_iff f hf
  have h2 := fp64_isZero_iff _ hg
  rw [fp64Pat_negate] at h2
  rw [Bool.eq_iff_iff, h1, h2]

end Negate


/-- Computable binary64 `float_round roundTiesToEven toneg x` for a rational
    `x`.  Values at or beyond `threshold` overflow to an infinity.  Otherwise
    the result is the nearest finite float, ties to even, with a zero result's
    sign taken from `toneg`. -/
def holFp64RoundTiesToEven (toneg : Bool) (x : Rat) : HolFloat 52 11 :=
  if x ≤ -holFloatThreshold 52 11 then holFloatMinusInfinity 52 11
  else if x ≥ holFloatThreshold 52 11 then holFloatPlusInfinity 52 11
  else
    let a : HolFloat 52 11 :=
      if x < 0 then holFloatNegate (fp64OfPat false (fp64Nearest (-x * 2 ^ 1074)))
      else fp64OfPat false (fp64Nearest (x * 2 ^ 1074))
    if holFloatIsZero a then
      (if toneg then holFloatMinusZero 52 11 else holFloatPlusZero 52 11)
    else a

private theorem fp64_zero_select {c a z : HolFloat 52 11}
    (h1 : holFloatIsZero c = holFloatIsZero a) (h2 : holFloatIsZero a = false → c = a) :
    (if holFloatIsZero c then z else c) = (if holFloatIsZero a then z else a) := by
  rw [h1]
  cases ha : holFloatIsZero a
  · rw [h2 ha]
  · rfl

/-- The computable rounding agrees with HOL's choice-based
    `float_round roundTiesToEven` at binary64, for every rational input. -/
theorem holFloatRound_rte_fp64 (toneg : Bool) (x : Rat) :
    (holFloatRound .roundTiesToEven toneg x : HolFloat 52 11) = holFp64RoundTiesToEven toneg x := by
  unfold holFloatRound holRound holFp64RoundTiesToEven
  simp only
  by_cases h1 : x ≤ -holFloatThreshold 52 11
  · rw [if_pos h1, if_pos h1]
    have : holFloatIsZero (holFloatMinusInfinity 52 11) = false := by decide +kernel
    rw [this]; rfl
  rw [if_neg h1, if_neg h1]
  by_cases h2 : x ≥ holFloatThreshold 52 11
  · rw [if_pos h2, if_pos h2]
    have : holFloatIsZero (holFloatPlusInfinity 52 11) = false := by decide +kernel
    rw [this]; rfl
  rw [if_neg h2, if_neg h2]
  have hth : x < holFloatThreshold 52 11 := by grind
  have hth' : -x < holFloatThreshold 52 11 := by grind
  -- the choice meets HOL's predicate once a witness is known
  have hspec : ∀ a : HolFloat 52 11, fp64RtePred x a →
      fp64RtePred x (holClosestSuch (fun a => a.significand.getLsbD 0 = false)
        (fun a => holFloatIsFinite a = true) x) :=
    fun a ha => holClosestSuch_spec _ _ _ ⟨a, ha⟩
  by_cases hneg : x < 0
  · rw [if_pos hneg]
    have hx : 0 ≤ -x := by grind
    obtain ⟨hPa', hall⟩ := fp64_rte_core hx hth'
    generalize fp64OfPat false (fp64Nearest (-x * 2 ^ 1074)) = a' at hPa' hall
    have hPa : fp64RtePred x (holFloatNegate a') := by
      have := fp64RtePred_negate hPa'; rwa [Rat.neg_neg] at this
    have hc := hspec _ hPa
    generalize holClosestSuch (t := 52) (w := 11) _ _ x = c at hc ⊢
    have ⟨hz, hne⟩ := hall _ (fp64RtePred_negate hc)
    have hcfin : holFloatIsFinite c = true := hc.1.1
    have ha'fin : holFloatIsFinite a' = true := hPa'.1.1
    rw [holFloatIsZero_negate c hcfin] at hz
    apply fp64_zero_select
    · rw [hz, holFloatIsZero_negate a' ha'fin]
    · intro h
      rw [holFloatIsZero_negate a' ha'fin] at h
      have := hne h
      rw [← this, holFloatNegate_negate]
  · rw [if_neg hneg]
    have hx : 0 ≤ x := by grind
    obtain ⟨hPa, hall⟩ := fp64_rte_core hx hth
    generalize fp64OfPat false (fp64Nearest (x * 2 ^ 1074)) = a at hPa hall
    have hc := hspec _ hPa
    generalize holClosestSuch (t := 52) (w := 11) _ _ x = c at hc ⊢
    have ⟨hz, hne⟩ := hall _ hc
    exact fp64_zero_select hz hne

end Flapjack
