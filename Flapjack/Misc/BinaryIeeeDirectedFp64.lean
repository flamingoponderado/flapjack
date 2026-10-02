import Flapjack.Misc.BinaryIeeeRoundFp64

/-!
# Binary64 directed rounding infrastructure

These computable bracket lemmas support agreement with the existing rational
rendering of the three directed HOL rounding clauses. HOL does not name this
algorithm, so these infrastructure declarations are untagged. They do not prove
cross-assistant agreement with HOL reals; SOUNDNESS item 8 still applies.
-/

namespace Flapjack.Binary64DirectedRounding

/-- Largest finite magnitude in subnormal units. -/
theorem fp64_largest_scaled :
    holFloatLargest 52 11 * 2 ^ 1074 = ((fp64N fp64MaxPat : Nat) : Rat) := by
  decide +kernel

/-- Lower adjacent magnitude pattern for a nonnegative scaled rational. -/
def fp64Lower (X : Rat) : Nat := fp64Bracket X.floor.toNat

/-- Upper adjacent pattern, retaining an exactly representable input. -/
def fp64Upper (X : Rat) : Nat :=
  if ((fp64N (fp64Lower X) : Nat) : Rat) = X then fp64Lower X
  else fp64Lower X + 1

/-- Both adjacent patterns enclose the scaled input, including exact inputs. -/
theorem fp64Directed_bracket {X : Rat} (hX : 0 ≤ X) :
    ((fp64N (fp64Lower X) : Nat) : Rat) ≤ X ∧
    X ≤ ((fp64N (fp64Upper X) : Nat) : Rat) := by
  have ⟨hlo, hhi⟩ := fp64Bracket_rat hX
  constructor
  · exact hlo
  · unfold fp64Upper
    split
    · next h => rw [h]; exact Rat.le_refl
    · exact Rat.le_of_lt hhi

/-- In the finite range, the lower bracket never exceeds the largest pattern. -/
theorem fp64Lower_le_max {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) :
    fp64Lower X ≤ fp64MaxPat := by
  have hlo := (fp64Directed_bracket hX).1
  apply Nat.le_of_not_lt
  intro h
  have hn : fp64N fp64MaxPat < fp64N (fp64Lower X) := fp64N_strictMono h
  have hc : ((fp64N fp64MaxPat : Nat) : Rat) <
      ((fp64N (fp64Lower X) : Nat) : Rat) := by exact_mod_cast hn
  grind

/-- The upper bracket also remains finite at the largest endpoint. -/
theorem fp64Upper_le_max {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) :
    fp64Upper X ≤ fp64MaxPat := by
  have hp := fp64Lower_le_max hX hmax
  have hlo := (fp64Directed_bracket hX).1
  unfold fp64Upper
  split
  · exact hp
  · next hne =>
      by_cases heq : fp64Lower X = fp64MaxPat
      · rw [heq] at hlo hne
        have : ((fp64N fp64MaxPat : Nat) : Rat) = X := by grind
        exact False.elim (hne this)
      · omega

/-- Value of a nonnegative magnitude pattern, without modular wraparound. -/
theorem fp64OfPat_positive_value {q : Nat} (hq : q < 2 ^ 63) :
    holFloatToReal (fp64OfPat false q) = ((fp64N q : Nat) : Rat) / 2 ^ 1074 := by
  rw [holFloatToReal_fp64, fp64Pat_ofPat false hq, fp64OfPat_sign_false]
  simp

/-- The two finite floats bracketing any nonnegative in-range scaled value. -/
theorem fp64Directed_finite_bracket {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) :
    holFloatIsFinite (fp64OfPat false (fp64Lower X)) = true ∧
    holFloatIsFinite (fp64OfPat false (fp64Upper X)) = true ∧
    holFloatToReal (fp64OfPat false (fp64Lower X)) ≤ X / 2 ^ 1074 ∧
    X / 2 ^ 1074 ≤ holFloatToReal (fp64OfPat false (fp64Upper X)) := by
  have hl := fp64Lower_le_max hX hmax
  have hu := fp64Upper_le_max hX hmax
  have hmax63 : fp64MaxPat < 2 ^ 63 := by decide
  have hlf : fp64Lower X < 2 ^ 63 := by omega
  have huf : fp64Upper X < 2 ^ 63 := by omega
  have hb := fp64Directed_bracket hX
  constructor
  · apply (fp64_isFinite_iff _).2
    rw [fp64Pat_ofPat false hlf]
    unfold fp64MaxPat at hl
    omega
  constructor
  · apply (fp64_isFinite_iff _).2
    rw [fp64Pat_ofPat false huf]
    unfold fp64MaxPat at hu
    omega
  rw [fp64OfPat_positive_value hlf, fp64OfPat_positive_value huf]
  constructor
  · exact Rat.mul_le_mul_of_nonneg_right hb.1 (Rat.le_of_lt (Rat.inv_pos.mpr fp64_D_pos))
  · exact Rat.mul_le_mul_of_nonneg_right hb.2 (Rat.le_of_lt (Rat.inv_pos.mpr fp64_D_pos))

/-- Every magnitude below the input lies at or below the lower bracket. -/
theorem fp64Lower_extremal {X : Rat} (hX : 0 ≤ X) {q : Nat}
    (hq : ((fp64N q : Nat) : Rat) ≤ X) : q ≤ fp64Lower X := by
  have hhi := (fp64Bracket_rat hX).2
  apply Nat.le_of_not_lt
  intro h
  have hn := fp64N_mono (show fp64Lower X + 1 ≤ q by omega)
  have hc : ((fp64N (fp64Lower X + 1) : Nat) : Rat) ≤
      ((fp64N q : Nat) : Rat) := by exact_mod_cast hn
  change X < ((fp64N (fp64Lower X + 1) : Nat) : Rat) at hhi
  grind

/-- Every magnitude above the input lies at or above the upper bracket. -/
theorem fp64Upper_extremal {X : Rat} (hX : 0 ≤ X) {q : Nat}
    (hq : X ≤ ((fp64N q : Nat) : Rat)) : fp64Upper X ≤ q := by
  have hlo := (fp64Directed_bracket hX).1
  have hp : fp64Lower X ≤ q := by
    apply Nat.le_of_not_lt
    intro h
    have hn := fp64N_strictMono h
    have hc : ((fp64N q : Nat) : Rat) <
        ((fp64N (fp64Lower X) : Nat) : Rat) := by exact_mod_cast hn
    grind
  unfold fp64Upper
  split
  · exact hp
  · next hne =>
      by_cases heq : fp64Lower X = q
      · rw [← heq] at hq
        have : ((fp64N (fp64Lower X) : Nat) : Rat) = X := by grind
        exact False.elim (hne this)
      · omega

/-- The lower float dominates every represented value below a nonnegative input. -/
theorem fp64Lower_value_extremal {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) (b : HolFloat 52 11)
    (hb : holFloatToReal b ≤ X / 2 ^ 1074) :
    holFloatToReal b ≤ holFloatToReal (fp64OfPat false (fp64Lower X)) := by
  have hl := fp64Lower_le_max hX hmax
  have hm : fp64MaxPat < 2 ^ 63 := by decide
  rw [fp64OfPat_positive_value (by omega), holFloatToReal_fp64] at *
  have hD := fp64_D_pos
  have hInv := Rat.inv_pos.mpr hD
  have hn0 : (0 : Rat) ≤ ((fp64N (fp64Pat b) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  have hl0 : (0 : Rat) ≤ ((fp64N (fp64Lower X) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  by_cases hs : b.sign = 1
  · simp only [hs, if_true] at hb ⊢
    apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt hInv)
    grind
  · simp only [hs, if_false, Rat.one_mul] at hb ⊢
    have hq : ((fp64N (fp64Pat b) : Nat) : Rat) ≤ X :=
      Rat.le_of_mul_le_mul_right hb hInv
    have hp := fp64Lower_extremal hX hq
    have hn := fp64N_mono hp
    have hc : ((fp64N (fp64Pat b) : Nat) : Rat) ≤
        ((fp64N (fp64Lower X) : Nat) : Rat) := by exact_mod_cast hn
    exact Rat.mul_le_mul_of_nonneg_right hc (Rat.le_of_lt hInv)

/-- The upper float is below every represented value above a nonnegative input. -/
theorem fp64Upper_value_extremal {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) (b : HolFloat 52 11)
    (hb : X / 2 ^ 1074 ≤ holFloatToReal b) :
    holFloatToReal (fp64OfPat false (fp64Upper X)) ≤ holFloatToReal b := by
  have hu := fp64Upper_le_max hX hmax
  have hm : fp64MaxPat < 2 ^ 63 := by decide
  rw [fp64OfPat_positive_value (by omega), holFloatToReal_fp64] at *
  have hD := fp64_D_pos
  have hInv := Rat.inv_pos.mpr hD
  have hn0 : (0 : Rat) ≤ ((fp64N (fp64Pat b) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  by_cases hs : b.sign = 1
  · simp only [hs, if_true] at hb ⊢
    have hxn := Rat.le_of_mul_le_mul_right hb hInv
    have hx0 : X = 0 := by grind
    have hp : fp64Upper X ≤ 0 := fp64Upper_extremal hX (by simp [hx0, fp64N])
    have hp0 : fp64Upper X = 0 := by omega
    rw [hp0]
    have hnzero : fp64N 0 = 0 := by decide
    rw [hnzero]
    change (0 : Rat) / 2 ^ 1074 ≤ -1 * ((fp64N (fp64Pat b) : Nat) : Rat) / 2 ^ 1074
    simpa only [hx0] using hb
  · simp only [hs, if_false, Rat.one_mul] at hb ⊢
    have hq : X ≤ ((fp64N (fp64Pat b) : Nat) : Rat) :=
      Rat.le_of_mul_le_mul_right hb hInv
    have hp := fp64Upper_extremal hX hq
    have hn := fp64N_mono hp
    have hc : ((fp64N (fp64Upper X) : Nat) : Rat) ≤
        ((fp64N (fp64Pat b) : Nat) : Rat) := by exact_mod_cast hn
    exact Rat.mul_le_mul_of_nonneg_right hc (Rat.le_of_lt hInv)

/-- The lower bracket satisfies the literal finite/below closest predicate. -/
theorem fp64Lower_isClosest {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) :
    holIsClosest (fun b : HolFloat 52 11 =>
      holFloatIsFinite b = true ∧ holFloatToReal b ≤ X / 2 ^ 1074)
      (X / 2 ^ 1074) (fp64OfPat false (fp64Lower X)) := by
  have hf := fp64Directed_finite_bracket hX hmax
  constructor
  · exact ⟨hf.1, hf.2.2.1⟩
  · intro b hb
    have he := fp64Lower_value_extremal hX hmax b hb.2
    unfold holRatAbs
    split <;> split <;> grind

/-- The upper bracket satisfies the literal finite/above closest predicate. -/
theorem fp64Upper_isClosest {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) :
    holIsClosest (fun b : HolFloat 52 11 =>
      holFloatIsFinite b = true ∧ X / 2 ^ 1074 ≤ holFloatToReal b)
      (X / 2 ^ 1074) (fp64OfPat false (fp64Upper X)) := by
  have hf := fp64Directed_finite_bracket hX hmax
  constructor
  · exact ⟨hf.2.1, hf.2.2.2⟩
  · intro b hb
    have he := fp64Upper_value_extremal hX hmax b hb.2
    unfold holRatAbs
    split <;> split <;> grind

/-- The lower bracket also satisfies toward-zero's absolute-value restriction. -/
theorem fp64Lower_zero_isClosest {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) :
    holIsClosest (fun b : HolFloat 52 11 =>
      holFloatIsFinite b = true ∧
        holRatAbs (holFloatToReal b) ≤ holRatAbs (X / 2 ^ 1074))
      (X / 2 ^ 1074) (fp64OfPat false (fp64Lower X)) := by
  have hf := fp64Directed_finite_bracket hX hmax
  have hl := fp64Lower_le_max hX hmax
  have hm : fp64MaxPat < 2 ^ 63 := by decide
  have hval := fp64OfPat_positive_value (q := fp64Lower X) (by omega)
  have hn0 : (0 : Rat) ≤ ((fp64N (fp64Lower X) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  have hD := fp64_D_pos
  have hInv := Rat.inv_pos.mpr hD
  have hv0 : 0 ≤ holFloatToReal (fp64OfPat false (fp64Lower X)) := by
    rw [hval]
    exact Rat.mul_nonneg hn0 (Rat.le_of_lt hInv)
  have hx0 : 0 ≤ X / 2 ^ 1074 := Rat.mul_nonneg hX (Rat.le_of_lt hInv)
  constructor
  · constructor
    · exact hf.1
    · unfold holRatAbs
      split <;> split <;> grind
  · intro b hb
    have hbbelow : holFloatToReal b ≤ X / 2 ^ 1074 := by
      have ha := hb.2
      unfold holRatAbs at ha
      split at ha <;> split at ha <;> grind
    exact (fp64Lower_isClosest hX hmax).2 b ⟨hb.1, hbbelow⟩

/-- All closest below-candidates have the lower bracket's represented value. -/
theorem fp64Lower_closest_value {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) (b : HolFloat 52 11)
    (hb : holIsClosest (fun c : HolFloat 52 11 =>
      holFloatIsFinite c = true ∧ holFloatToReal c ≤ X / 2 ^ 1074)
      (X / 2 ^ 1074) b) :
    holFloatToReal b = holFloatToReal (fp64OfPat false (fp64Lower X)) := by
  have hc := fp64Lower_isClosest hX hmax
  have hd := hb.2 _ hc.1
  have he := fp64Lower_value_extremal hX hmax b hb.1.2
  have hl := hc.1.2
  have hbval := hb.1.2
  unfold holRatAbs at hd
  split at hd <;> split at hd <;> grind

/-- All closest above-candidates have the upper bracket's represented value. -/
theorem fp64Upper_closest_value {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) (b : HolFloat 52 11)
    (hb : holIsClosest (fun c : HolFloat 52 11 =>
      holFloatIsFinite c = true ∧ X / 2 ^ 1074 ≤ holFloatToReal c)
      (X / 2 ^ 1074) b) :
    holFloatToReal b = holFloatToReal (fp64OfPat false (fp64Upper X)) := by
  have hc := fp64Upper_isClosest hX hmax
  have hd := hb.2 _ hc.1
  have he := fp64Upper_value_extremal hX hmax b hb.1.2
  have hl := hc.1.2
  have hbval := hb.1.2
  unfold holRatAbs at hd
  split at hd <;> split at hd <;> grind

/-- Toward-zero closest candidates have the same represented value as the lower bracket. -/
theorem fp64Lower_zero_closest_value {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) (b : HolFloat 52 11)
    (hb : holIsClosest (fun c : HolFloat 52 11 =>
      holFloatIsFinite c = true ∧
        holRatAbs (holFloatToReal c) ≤ holRatAbs (X / 2 ^ 1074))
      (X / 2 ^ 1074) b) :
    holFloatToReal b = holFloatToReal (fp64OfPat false (fp64Lower X)) := by
  have hc := fp64Lower_zero_isClosest hX hmax
  have hd := hb.2 _ hc.1
  have hf := fp64Directed_finite_bracket hX hmax
  have hD := fp64_D_pos
  have hInv := Rat.inv_pos.mpr hD
  have hx0 : 0 ≤ X / 2 ^ 1074 := Rat.mul_nonneg hX (Rat.le_of_lt hInv)
  have hbval : holFloatToReal b ≤ X / 2 ^ 1074 := by
    have ha := hb.1.2
    unfold holRatAbs at ha
    split at ha <;> split at ha <;> grind
  have he := fp64Lower_value_extremal hX hmax b hbval
  have hl := hf.2.2.1
  unfold holRatAbs at hd
  split at hd <;> split at hd <;> grind

/-- Equal represented magnitudes have equal patterns when their sign bits agree. -/
theorem fp64_same_sign_value_injective (a b : HolFloat 52 11)
    (hs : a.sign = b.sign) (hv : holFloatToReal a = holFloatToReal b) : a = b := by
  rw [holFloatToReal_fp64, holFloatToReal_fp64, hs] at hv
  have hD := fp64_D_pos
  have hInv := Rat.inv_pos.mpr hD
  have hn : ((fp64N (fp64Pat a) : Nat) : Rat) =
      ((fp64N (fp64Pat b) : Nat) : Rat) := by
    by_cases h : b.sign = 1 <;> simp only [h, if_true, if_false] at hv <;> grind
  have hnat : fp64N (fp64Pat a) = fp64N (fp64Pat b) := by exact_mod_cast hn
  have hp : fp64Pat a = fp64Pat b := by
    rcases Nat.lt_trichotomy (fp64Pat a) (fp64Pat b) with h | h | h
    · have := fp64N_strictMono h; omega
    · exact h
    · have := fp64N_strictMono h; omega
  rw [← fp64OfPat_pat a, ← fp64OfPat_pat b, hs, hp]

/-- Finite zero classification depends only on the represented value. -/
theorem fp64_finite_zero_value (f : HolFloat 52 11)
    (hf : holFloatIsFinite f = true) :
    holFloatIsZero f = true ↔ holFloatToReal f = 0 := by
  rw [fp64_isZero_iff f hf]
  rw [holFloatToReal_fp64]
  have hD := fp64_D_pos
  have hInv := Rat.inv_pos.mpr hD
  constructor
  · intro hp
    rw [hp]
    have hz : fp64N 0 = 0 := by decide
    rw [hz]
    grind
  · intro hv
    have hn : ((fp64N (fp64Pat f) : Nat) : Rat) = 0 := by
      by_cases hs : f.sign = 1 <;> simp only [hs, if_true, if_false] at hv <;> grind
    have hn' : fp64N (fp64Pat f) = 0 := by exact_mod_cast hn
    exact fp64N_eq_zero.mp hn'

/-- Nonzero equal values force equal signs; the only sign ambiguity is zero. -/
theorem fp64_equal_nonzero_value (a b : HolFloat 52 11)
    (hv : holFloatToReal a = holFloatToReal b)
    (hn : holFloatToReal b ≠ 0) : a = b := by
  apply fp64_same_sign_value_injective a b _ hv
  have ha : a.sign = 0 ∨ a.sign = 1 := by
    have h := a.sign.isLt
    have : a.sign.toNat = 0 ∨ a.sign.toNat = 1 := by omega
    rcases this with h | h
    · left; exact BitVec.eq_of_toNat_eq (by simpa using h)
    · right; exact BitVec.eq_of_toNat_eq (by simpa using h)
  have hb : b.sign = 0 ∨ b.sign = 1 := by
    have h := b.sign.isLt
    have : b.sign.toNat = 0 ∨ b.sign.toNat = 1 := by omega
    rcases this with h | h
    · left; exact BitVec.eq_of_toNat_eq (by simpa using h)
    · right; exact BitVec.eq_of_toNat_eq (by simpa using h)
  have hD := fp64_D_pos
  have hInv := Rat.inv_pos.mpr hD
  have hna : (0 : Rat) ≤ ((fp64N (fp64Pat a) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  have hnb : (0 : Rat) ≤ ((fp64N (fp64Pat b) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  rw [holFloatToReal_fp64, holFloatToReal_fp64] at hv
  rw [holFloatToReal_fp64] at hn
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [ha, hb]
  · simp only [ha, hb] at hv hn
    have he := congrArg (fun y : Rat => y * 2 ^ 1074) hv
    have hDz : (2 ^ 1074 : Rat) ≠ 0 := by grind
    rw [Rat.div_mul_cancel hDz, Rat.div_mul_cancel hDz] at he
    have hbzero : ((fp64N (fp64Pat b) : Nat) : Rat) = 0 := by grind
    rw [hbzero] at hn
    simp [Rat.div_def] at hn
  · simp only [ha, hb] at hv hn
    have he := congrArg (fun y : Rat => y * 2 ^ 1074) hv
    have hDz : (2 ^ 1074 : Rat) ≠ 0 := by grind
    rw [Rat.div_mul_cancel hDz, Rat.div_mul_cancel hDz] at he
    have hbzero : ((fp64N (fp64Pat b) : Nat) : Rat) = 0 := by grind
    rw [hbzero] at hn
    simp [Rat.div_def] at hn
  · rw [ha, hb]

/-- Equal finite represented values become equal records after zero-sign selection. -/
theorem fp64_zero_sign_value_eq (a b : HolFloat 52 11)
    (ha : holFloatIsFinite a = true) (hb : holFloatIsFinite b = true)
    (hv : holFloatToReal a = holFloatToReal b) (z : HolFloat 52 11) :
    (if holFloatIsZero a then z else a) =
      (if holFloatIsZero b then z else b) := by
  have hz : holFloatIsZero a = holFloatIsZero b := by
    have he : holFloatIsZero a = true ↔ holFloatIsZero b = true := by
      rw [fp64_finite_zero_value a ha, fp64_finite_zero_value b hb, hv]
    cases hza : holFloatIsZero a <;> cases hzb : holFloatIsZero b <;> simp_all
  rw [hz]
  cases hzb : holFloatIsZero b
  · have hn : holFloatToReal b ≠ 0 := by
      intro h
      have := (fp64_finite_zero_value b hb).2 h
      rw [hzb] at this
      contradiction
    rw [fp64_equal_nonzero_value a b hv hn]
  · rfl

/-- A witnessed closest candidate discharges the choice specification. -/
theorem fp64_closest_spec (s : HolFloat 52 11 → Prop) (x : Rat)
    (a : HolFloat 52 11) (ha : holIsClosest s x a) :
    holIsClosest s x (holClosest s x) := by
  unfold holClosest
  apply (holClosestSuch_spec (fun _ => True) s x _).1
  exact ⟨a, ha, fun _ _ => True.intro⟩

/-- Negation transports any closest predicate whose candidates are transported. -/
theorem fp64_closest_negate (s r : HolFloat 52 11 → Prop) (x : Rat)
    (c : HolFloat 52 11)
    (hc : holIsClosest s x c)
    (hforward : ∀ a, s a → r (holFloatNegate a))
    (hbackward : ∀ b, r b → s (holFloatNegate b)) :
    holIsClosest r (-x) (holFloatNegate c) := by
  refine ⟨hforward c hc.1, fun b hb => ?_⟩
  have hd := hc.2 (holFloatNegate b) (hbackward b hb)
  rw [holFloatToReal_negate] at hd
  rw [holFloatToReal_negate]
  have e1 : -holFloatToReal c - -x = -(holFloatToReal c - x) := by grind
  have e2 : -holFloatToReal b - x = -(holFloatToReal b - -x) := by grind
  rw [e1, holRatAbs_neg]
  rw [e2, holRatAbs_neg] at hd
  exact hd

/-- Negation swaps below and above candidate sets, including their finite guard. -/
theorem fp64_below_closest_negate (x : Rat) (c : HolFloat 52 11)
    (hc : holIsClosest (fun a : HolFloat 52 11 =>
      holFloatIsFinite a = true ∧ holFloatToReal a ≤ x) x c) :
    holIsClosest (fun a : HolFloat 52 11 =>
      holFloatIsFinite a = true ∧ -x ≤ holFloatToReal a)
      (-x) (holFloatNegate c) := by
  apply fp64_closest_negate _ _ x c hc
  · intro a ha
    rw [holFloatIsFinite_negate, holFloatToReal_negate]
    exact ⟨ha.1, by grind⟩
  · intro b hb
    rw [holFloatIsFinite_negate, holFloatToReal_negate]
    exact ⟨hb.1, by grind⟩

/-- Negation transports toward-zero's absolute-value candidate set unchanged. -/
theorem fp64_zero_closest_negate (x : Rat) (c : HolFloat 52 11)
    (hc : holIsClosest (fun a : HolFloat 52 11 =>
      holFloatIsFinite a = true ∧ holRatAbs (holFloatToReal a) ≤ holRatAbs x) x c) :
    holIsClosest (fun a : HolFloat 52 11 =>
      holFloatIsFinite a = true ∧ holRatAbs (holFloatToReal a) ≤ holRatAbs (-x))
      (-x) (holFloatNegate c) := by
  apply fp64_closest_negate _ _ x c hc
  · intro a ha
    rw [holFloatIsFinite_negate, holFloatToReal_negate, holRatAbs_neg, holRatAbs_neg]
    exact ha
  · intro b hb
    rw [holFloatIsFinite_negate, holFloatToReal_negate, holRatAbs_neg]
    rw [holRatAbs_neg] at hb
    exact hb

/-- Negation swaps above candidates to below candidates. -/
theorem fp64_above_closest_negate (x : Rat) (c : HolFloat 52 11)
    (hc : holIsClosest (fun a : HolFloat 52 11 =>
      holFloatIsFinite a = true ∧ x ≤ holFloatToReal a) x c) :
    holIsClosest (fun a : HolFloat 52 11 =>
      holFloatIsFinite a = true ∧ holFloatToReal a ≤ -x)
      (-x) (holFloatNegate c) := by
  apply fp64_closest_negate _ _ x c hc
  · intro a ha
    rw [holFloatIsFinite_negate, holFloatToReal_negate]
    exact ⟨ha.1, by grind⟩
  · intro b hb
    rw [holFloatIsFinite_negate, holFloatToReal_negate]
    exact ⟨hb.1, by grind⟩

/-- The three directed cases; nearest-even is proved in the imported module. -/
inductive Fp64Direction where
  | zero | positive | negative
  deriving DecidableEq

/-- Literal directed finite candidate predicates from HOL's three clauses. -/
def fp64DirectedCandidates (d : Fp64Direction) (x : Rat) (b : HolFloat 52 11) : Prop :=
  holFloatIsFinite b = true ∧ match d with
    | .zero => holRatAbs (holFloatToReal b) ≤ holRatAbs x
    | .positive => x ≤ holFloatToReal b
    | .negative => holFloatToReal b ≤ x

/-- Computable positive-domain directed magnitude selection. -/
def fp64DirectedPositive (d : Fp64Direction) (X : Rat) : HolFloat 52 11 :=
  fp64OfPat false (match d with
    | .positive => fp64Upper X
    | .zero | .negative => fp64Lower X)

/-- Positive-domain selection is closest in the exact directed candidate set. -/
theorem fp64DirectedPositive_closest (d : Fp64Direction) {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) :
    holIsClosest (fp64DirectedCandidates d (X / 2 ^ 1074))
      (X / 2 ^ 1074) (fp64DirectedPositive d X) := by
  cases d
  · exact fp64Lower_zero_isClosest hX hmax
  · exact fp64Upper_isClosest hX hmax
  · exact fp64Lower_isClosest hX hmax

/-- Every directed closest candidate has the computed positive bracket's value. -/
theorem fp64DirectedPositive_closest_value (d : Fp64Direction) {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) (b : HolFloat 52 11)
    (hb : holIsClosest (fp64DirectedCandidates d (X / 2 ^ 1074)) (X / 2 ^ 1074) b) :
    holFloatToReal b = holFloatToReal (fp64DirectedPositive d X) := by
  cases d
  · exact fp64Lower_zero_closest_value hX hmax b hb
  · exact fp64Upper_closest_value hX hmax b hb
  · exact fp64Lower_closest_value hX hmax b hb

/-- Positive-domain selection is finite, including the largest endpoint. -/
theorem fp64DirectedPositive_finite (d : Fp64Direction) {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) :
    holFloatIsFinite (fp64DirectedPositive d X) = true := by
  have hf := fp64Directed_finite_bracket hX hmax
  cases d
  · exact hf.1
  · exact hf.2.1
  · exact hf.1

/-- Choice-based and computed directed candidates agree after selecting zero's sign. -/
theorem fp64DirectedPositive_choice (d : Fp64Direction) {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) (z : HolFloat 52 11) :
    let c := holClosest (fp64DirectedCandidates d (X / 2 ^ 1074)) (X / 2 ^ 1074)
    let a := fp64DirectedPositive d X
    (if holFloatIsZero c then z else c) = (if holFloatIsZero a then z else a) := by
  have hc := fp64_closest_spec _ _ _ (fp64DirectedPositive_closest d hX hmax)
  have hv := fp64DirectedPositive_closest_value d hX hmax _ hc
  have hf : holFloatIsFinite
      (holClosest (fp64DirectedCandidates d (X / 2 ^ 1074)) (X / 2 ^ 1074)) = true := hc.1.1
  exact fp64_zero_sign_value_eq _ _ hf (fp64DirectedPositive_finite d hX hmax) hv z

/-- Negation exchanges upward and downward rounding. -/
def fp64FlipDirection : Fp64Direction → Fp64Direction
  | .zero => .zero
  | .positive => .negative
  | .negative => .positive

/-- Directed candidate sets transform exactly under sign reversal. -/
theorem fp64DirectedCandidates_negate (d : Fp64Direction) (x : Rat) (b : HolFloat 52 11) :
    fp64DirectedCandidates d (-x) (holFloatNegate b) ↔
      fp64DirectedCandidates (fp64FlipDirection d) x b := by
  unfold fp64DirectedCandidates
  rw [holFloatIsFinite_negate, holFloatToReal_negate]
  cases d <;> simp only [fp64FlipDirection]
  · rw [holRatAbs_neg, holRatAbs_neg]
  · constructor <;> intro h <;> exact ⟨h.1, by grind⟩
  · constructor <;> intro h <;> exact ⟨h.1, by grind⟩

/-- The negative-domain computed candidate satisfies the exact closest predicate. -/
theorem fp64DirectedNegative_closest (d : Fp64Direction) {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) :
    holIsClosest (fp64DirectedCandidates d (-(X / 2 ^ 1074)))
      (-(X / 2 ^ 1074))
      (holFloatNegate (fp64DirectedPositive (fp64FlipDirection d) X)) := by
  apply fp64_closest_negate _ _ _ _
    (fp64DirectedPositive_closest (fp64FlipDirection d) hX hmax)
  · intro a ha
    exact (fp64DirectedCandidates_negate d _ a).2 ha
  · intro b hb
    have h := (fp64DirectedCandidates_negate d (X / 2 ^ 1074) (holFloatNegate b)).1
    rw [holFloatNegate_negate] at h
    exact h hb

/-- Negative-domain closest candidates share the computed negative bracket's value. -/
theorem fp64DirectedNegative_closest_value (d : Fp64Direction) {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) (b : HolFloat 52 11)
    (hb : holIsClosest (fp64DirectedCandidates d (-(X / 2 ^ 1074)))
      (-(X / 2 ^ 1074)) b) :
    holFloatToReal b =
      holFloatToReal (holFloatNegate (fp64DirectedPositive (fp64FlipDirection d) X)) := by
  have hn : holIsClosest (fp64DirectedCandidates (fp64FlipDirection d) (X / 2 ^ 1074))
      (X / 2 ^ 1074) (holFloatNegate b) := by
    have h := fp64_closest_negate _ _ (-(X / 2 ^ 1074)) b hb
      (fun a ha => (fp64DirectedCandidates_negate d (X / 2 ^ 1074) (holFloatNegate a)).1
        (by simpa only [holFloatNegate_negate] using ha))
      (fun c hc => (fp64DirectedCandidates_negate d (X / 2 ^ 1074) c).2 hc)
    simpa only [Rat.neg_neg] using h
  have hv := fp64DirectedPositive_closest_value (fp64FlipDirection d) hX hmax _ hn
  rw [holFloatToReal_negate] at hv
  rw [holFloatToReal_negate]
  grind

/-- Negative-domain choice agrees with the computed candidate after zero-sign selection. -/
theorem fp64DirectedNegative_choice (d : Fp64Direction) {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp64N fp64MaxPat : Nat) : Rat)) (z : HolFloat 52 11) :
    let c := holClosest (fp64DirectedCandidates d (-(X / 2 ^ 1074))) (-(X / 2 ^ 1074))
    let a := holFloatNegate (fp64DirectedPositive (fp64FlipDirection d) X)
    (if holFloatIsZero c then z else c) = (if holFloatIsZero a then z else a) := by
  have hc := fp64_closest_spec _ _ _ (fp64DirectedNegative_closest d hX hmax)
  have hv := fp64DirectedNegative_closest_value d hX hmax _ hc
  have hf : holFloatIsFinite
      (holClosest (fp64DirectedCandidates d (-(X / 2 ^ 1074))) (-(X / 2 ^ 1074))) = true := hc.1.1
  have ha : holFloatIsFinite
      (holFloatNegate (fp64DirectedPositive (fp64FlipDirection d) X)) = true := by
    rw [holFloatIsFinite_negate]
    exact fp64DirectedPositive_finite _ hX hmax
  exact fp64_zero_sign_value_eq _ _ hf ha hv z

/-- Computable signed in-range candidate for the directed modes. -/
def fp64DirectedCandidate (d : Fp64Direction) (x : Rat) : HolFloat 52 11 :=
  if x < 0 then
    holFloatNegate (fp64DirectedPositive (fp64FlipDirection d) (-x * 2 ^ 1074))
  else fp64DirectedPositive d (x * 2 ^ 1074)

/-- Choice agrees with the computable signed candidate throughout the finite interval. -/
theorem fp64DirectedCandidate_choice (d : Fp64Direction) (x : Rat)
    (hlo : -holFloatLargest 52 11 ≤ x) (hhi : x ≤ holFloatLargest 52 11)
    (z : HolFloat 52 11) :
    let c := holClosest (fp64DirectedCandidates d x) x
    let a := fp64DirectedCandidate d x
    (if holFloatIsZero c then z else c) = (if holFloatIsZero a then z else a) := by
  have hD := fp64_D_pos
  have hInv := Rat.inv_pos.mpr hD
  unfold fp64DirectedCandidate
  split
  · next hx =>
      have hX : 0 ≤ -x * 2 ^ 1074 := by grind
      have hM : -x * 2 ^ 1074 ≤ ((fp64N fp64MaxPat : Nat) : Rat) := by
        rw [← fp64_largest_scaled]
        grind
      have he : -((-x * 2 ^ 1074) / 2 ^ 1074) = x := by grind
      have h := fp64DirectedNegative_choice d hX hM z
      rw [he] at h
      exact h
  · next hx =>
      have hX : 0 ≤ x * 2 ^ 1074 := by grind
      have hM : x * 2 ^ 1074 ≤ ((fp64N fp64MaxPat : Nat) : Rat) := by
        rw [← fp64_largest_scaled]
        grind
      have he : (x * 2 ^ 1074) / 2 ^ 1074 = x := by grind
      have h := fp64DirectedPositive_choice d hX hM z
      rw [he] at h
      exact h

/-- Original rounding mode corresponding to a directed case. -/
def fp64DirectionMode : Fp64Direction → HolRounding
  | .zero => .roundTowardZero
  | .positive => .roundTowardPositive
  | .negative => .roundTowardNegative

/-- Full computable directed rounding, retaining HOL's strict overflow guards. -/
def holFp64DirectedRound (d : Fp64Direction) (toneg : Bool) (x : Rat) : HolFloat 52 11 :=
  let a := if x < -holFloatLargest 52 11 then
      match d with
      | .negative => holFloatMinusInfinity 52 11
      | .zero | .positive => holFloatBottom 52 11
    else if x > holFloatLargest 52 11 then
      match d with
      | .positive => holFloatPlusInfinity 52 11
      | .zero | .negative => holFloatTop 52 11
    else fp64DirectedCandidate d x
  if holFloatIsZero a then
    (if toneg then holFloatMinusZero 52 11 else holFloatPlusZero 52 11)
  else a

/-- Full-domain directed agreement for every rational input and requested zero sign. -/
theorem holFloatRound_directed_fp64 (d : Fp64Direction) (toneg : Bool) (x : Rat) :
    (holFloatRound (fp64DirectionMode d) toneg x : HolFloat 52 11) =
      holFp64DirectedRound d toneg x := by
  have hlow := fp64DirectedCandidate_choice d x
  unfold holFloatRound holFp64DirectedRound
  by_cases hl : x < -holFloatLargest 52 11
  · cases d <;> simp only [fp64DirectionMode, holRound, hl, if_true]
  · by_cases hh : x > holFloatLargest 52 11
    · cases d <;> simp only [fp64DirectionMode, holRound, hl, hh, if_false, if_true]
    · have hlo : -holFloatLargest 52 11 ≤ x := by grind
      have hhi : x ≤ holFloatLargest 52 11 := by grind
      have h := hlow hlo hhi
        (if toneg then holFloatMinusZero 52 11 else holFloatPlusZero 52 11)
      cases d <;> dsimp [fp64DirectionMode, holRound, fp64DirectedCandidates] at h ⊢ <;>
        simp only [hl, hh, if_false] <;> exact h

end Flapjack.Binary64DirectedRounding

namespace Flapjack

/-- Computable binary64 rounding for all four original modes. This is untagged
infrastructure: HOL does not name this algorithm. Agreement below is with the
existing rational rendering; SOUNDNESS item 8 remains an external assumption. -/
def holFp64Round (mode : HolRounding) (toneg : Bool) (x : Rat) : HolFloat 52 11 :=
  match mode with
  | .roundTiesToEven => holFp64RoundTiesToEven toneg x
  | .roundTowardZero => Binary64DirectedRounding.holFp64DirectedRound .zero toneg x
  | .roundTowardPositive => Binary64DirectedRounding.holFp64DirectedRound .positive toneg x
  | .roundTowardNegative => Binary64DirectedRounding.holFp64DirectedRound .negative toneg x

/-- Complete binary64 agreement, with no additional premise, for every mode,
rational argument and requested zero sign. This does not establish cross-HOL
real equality, and therefore carries no original-declaration tag. -/
theorem holFloatRound_fp64 (mode : HolRounding) (toneg : Bool) (x : Rat) :
    (holFloatRound mode toneg x : HolFloat 52 11) = holFp64Round mode toneg x := by
  cases mode
  · exact holFloatRound_rte_fp64 toneg x
  · exact Binary64DirectedRounding.holFloatRound_directed_fp64 .positive toneg x
  · exact Binary64DirectedRounding.holFloatRound_directed_fp64 .negative toneg x
  · exact Binary64DirectedRounding.holFloatRound_directed_fp64 .zero toneg x

end Flapjack
