import Flapjack.Misc.BinaryIeeeRoundFp32

/-!
# Binary32 directed rounding infrastructure

These computable bracket lemmas support agreement with the existing rational
rendering of the three directed HOL rounding clauses. HOL does not name this
algorithm, so these infrastructure declarations are untagged. They do not prove
cross-assistant agreement with HOL reals; SOUNDNESS item 8 still applies.
-/

namespace Flapjack.Binary32Rounding

/-- Largest finite magnitude in subnormal units. -/
theorem fp32_largest_scaled :
    holFloatLargest 23 8 * 2 ^ 149 = ((fp32N fp32MaxPat : Nat) : Rat) := by
  decide +kernel

/-- Lower adjacent magnitude pattern for a nonnegative scaled rational. -/
def fp32Lower (X : Rat) : Nat := fp32Bracket X.floor.toNat

/-- Upper adjacent pattern, retaining an exactly representable input. -/
def fp32Upper (X : Rat) : Nat :=
  if ((fp32N (fp32Lower X) : Nat) : Rat) = X then fp32Lower X
  else fp32Lower X + 1

/-- Both adjacent patterns enclose the scaled input, including exact inputs. -/
theorem fp32Directed_bracket {X : Rat} (hX : 0 ≤ X) :
    ((fp32N (fp32Lower X) : Nat) : Rat) ≤ X ∧
    X ≤ ((fp32N (fp32Upper X) : Nat) : Rat) := by
  have ⟨hlo, hhi⟩ := fp32Bracket_rat hX
  constructor
  · exact hlo
  · unfold fp32Upper
    split
    · next h => rw [h]; exact Rat.le_refl
    · exact Rat.le_of_lt hhi

/-- In the finite range, the lower bracket never exceeds the largest pattern. -/
theorem fp32Lower_le_max {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) :
    fp32Lower X ≤ fp32MaxPat := by
  have hlo := (fp32Directed_bracket hX).1
  apply Nat.le_of_not_lt
  intro h
  have hn : fp32N fp32MaxPat < fp32N (fp32Lower X) := fp32N_strictMono h
  have hc : ((fp32N fp32MaxPat : Nat) : Rat) <
      ((fp32N (fp32Lower X) : Nat) : Rat) := by exact_mod_cast hn
  grind

/-- The upper bracket also remains finite at the largest endpoint. -/
theorem fp32Upper_le_max {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) :
    fp32Upper X ≤ fp32MaxPat := by
  have hp := fp32Lower_le_max hX hmax
  have hlo := (fp32Directed_bracket hX).1
  unfold fp32Upper
  split
  · exact hp
  · next hne =>
      by_cases heq : fp32Lower X = fp32MaxPat
      · rw [heq] at hlo hne
        have : ((fp32N fp32MaxPat : Nat) : Rat) = X := by grind
        exact False.elim (hne this)
      · omega

/-- Value of a nonnegative magnitude pattern, without modular wraparound. -/
theorem fp32OfPat_positive_value {q : Nat} (hq : q < 2 ^ 31) :
    holFloatToReal (fp32OfPat false q) = ((fp32N q : Nat) : Rat) / 2 ^ 149 := by
  rw [holFloatToReal_fp32, fp32Pat_ofPat false hq, fp32OfPat_sign_false]
  simp

/-- The two finite floats bracketing any nonnegative in-range scaled value. -/
theorem fp32Directed_finite_bracket {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) :
    holFloatIsFinite (fp32OfPat false (fp32Lower X)) = true ∧
    holFloatIsFinite (fp32OfPat false (fp32Upper X)) = true ∧
    holFloatToReal (fp32OfPat false (fp32Lower X)) ≤ X / 2 ^ 149 ∧
    X / 2 ^ 149 ≤ holFloatToReal (fp32OfPat false (fp32Upper X)) := by
  have hl := fp32Lower_le_max hX hmax
  have hu := fp32Upper_le_max hX hmax
  have hmax31 : fp32MaxPat < 2 ^ 31 := by decide
  have hlf : fp32Lower X < 2 ^ 31 := by omega
  have huf : fp32Upper X < 2 ^ 31 := by omega
  have hb := fp32Directed_bracket hX
  constructor
  · apply (fp32_isFinite_iff _).2
    rw [fp32Pat_ofPat false hlf]
    unfold fp32MaxPat at hl
    omega
  constructor
  · apply (fp32_isFinite_iff _).2
    rw [fp32Pat_ofPat false huf]
    unfold fp32MaxPat at hu
    omega
  rw [fp32OfPat_positive_value hlf, fp32OfPat_positive_value huf]
  constructor
  · have hD := fp32_D_pos
    grind
  · have hD := fp32_D_pos
    grind

/-- Every magnitude below the input lies at or below the lower bracket. -/
theorem fp32Lower_extremal {X : Rat} (hX : 0 ≤ X) {q : Nat}
    (hq : ((fp32N q : Nat) : Rat) ≤ X) : q ≤ fp32Lower X := by
  have hhi := (fp32Bracket_rat hX).2
  apply Nat.le_of_not_lt
  intro h
  have hn := fp32N_mono (show fp32Lower X + 1 ≤ q by omega)
  have hc : ((fp32N (fp32Lower X + 1) : Nat) : Rat) ≤
      ((fp32N q : Nat) : Rat) := by exact_mod_cast hn
  change X < ((fp32N (fp32Lower X + 1) : Nat) : Rat) at hhi
  grind

/-- Every magnitude above the input lies at or above the upper bracket. -/
theorem fp32Upper_extremal {X : Rat} (hX : 0 ≤ X) {q : Nat}
    (hq : X ≤ ((fp32N q : Nat) : Rat)) : fp32Upper X ≤ q := by
  have hlo := (fp32Directed_bracket hX).1
  have hp : fp32Lower X ≤ q := by
    apply Nat.le_of_not_lt
    intro h
    have hn := fp32N_strictMono h
    have hc : ((fp32N q : Nat) : Rat) <
        ((fp32N (fp32Lower X) : Nat) : Rat) := by exact_mod_cast hn
    grind
  unfold fp32Upper
  split
  · exact hp
  · next hne =>
      by_cases heq : fp32Lower X = q
      · rw [← heq] at hq
        have : ((fp32N (fp32Lower X) : Nat) : Rat) = X := by grind
        exact False.elim (hne this)
      · omega

/-- The lower float dominates every represented value below a nonnegative input. -/
theorem fp32Lower_value_extremal {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) (b : HolFloat 23 8)
    (hb : holFloatToReal b ≤ X / 2 ^ 149) :
    holFloatToReal b ≤ holFloatToReal (fp32OfPat false (fp32Lower X)) := by
  have hl := fp32Lower_le_max hX hmax
  have hm : fp32MaxPat < 2 ^ 31 := by decide
  rw [fp32OfPat_positive_value (by omega), holFloatToReal_fp32] at *
  have hD := fp32_D_pos
  have hn0 : (0 : Rat) ≤ ((fp32N (fp32Pat b) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  have hl0 : (0 : Rat) ≤ ((fp32N (fp32Lower X) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  by_cases hs : b.sign = 1
  · simp only [hs, if_true] at hb ⊢
    grind
  · simp only [hs, if_false, Rat.one_mul] at hb ⊢
    have hq : ((fp32N (fp32Pat b) : Nat) : Rat) ≤ X := by grind
    have hp := fp32Lower_extremal hX hq
    have hn := fp32N_mono hp
    have hc : ((fp32N (fp32Pat b) : Nat) : Rat) ≤
        ((fp32N (fp32Lower X) : Nat) : Rat) := by exact_mod_cast hn
    grind

/-- The upper float is below every represented value above a nonnegative input. -/
theorem fp32Upper_value_extremal {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) (b : HolFloat 23 8)
    (hb : X / 2 ^ 149 ≤ holFloatToReal b) :
    holFloatToReal (fp32OfPat false (fp32Upper X)) ≤ holFloatToReal b := by
  have hu := fp32Upper_le_max hX hmax
  have hm : fp32MaxPat < 2 ^ 31 := by decide
  rw [fp32OfPat_positive_value (by omega), holFloatToReal_fp32] at *
  have hD := fp32_D_pos
  have hn0 : (0 : Rat) ≤ ((fp32N (fp32Pat b) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  by_cases hs : b.sign = 1
  · simp only [hs, if_true] at hb ⊢
    have hx0 : X = 0 := by grind
    have hp : fp32Upper X ≤ 0 := fp32Upper_extremal hX (by simp [hx0, fp32N])
    have hp0 : fp32Upper X = 0 := by omega
    rw [hp0]
    have hnzero : fp32N 0 = 0 := by decide
    rw [hnzero]
    change (0 : Rat) / 2 ^ 149 ≤ -1 * ((fp32N (fp32Pat b) : Nat) : Rat) / 2 ^ 149
    grind
  · simp only [hs, if_false, Rat.one_mul] at hb ⊢
    have hq : X ≤ ((fp32N (fp32Pat b) : Nat) : Rat) := by grind
    have hp := fp32Upper_extremal hX hq
    have hn := fp32N_mono hp
    have hc : ((fp32N (fp32Upper X) : Nat) : Rat) ≤
        ((fp32N (fp32Pat b) : Nat) : Rat) := by exact_mod_cast hn
    grind

/-- The lower bracket satisfies the literal finite/below closest predicate. -/
theorem fp32Lower_isClosest {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) :
    holIsClosest (fun b : HolFloat 23 8 =>
      holFloatIsFinite b = true ∧ holFloatToReal b ≤ X / 2 ^ 149)
      (X / 2 ^ 149) (fp32OfPat false (fp32Lower X)) := by
  have hf := fp32Directed_finite_bracket hX hmax
  constructor
  · exact ⟨hf.1, hf.2.2.1⟩
  · intro b hb
    have he := fp32Lower_value_extremal hX hmax b hb.2
    unfold holRatAbs
    split <;> split <;> grind

/-- The upper bracket satisfies the literal finite/above closest predicate. -/
theorem fp32Upper_isClosest {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) :
    holIsClosest (fun b : HolFloat 23 8 =>
      holFloatIsFinite b = true ∧ X / 2 ^ 149 ≤ holFloatToReal b)
      (X / 2 ^ 149) (fp32OfPat false (fp32Upper X)) := by
  have hf := fp32Directed_finite_bracket hX hmax
  constructor
  · exact ⟨hf.2.1, hf.2.2.2⟩
  · intro b hb
    have he := fp32Upper_value_extremal hX hmax b hb.2
    unfold holRatAbs
    split <;> split <;> grind

/-- The lower bracket also satisfies toward-zero's absolute-value restriction. -/
theorem fp32Lower_zero_isClosest {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) :
    holIsClosest (fun b : HolFloat 23 8 =>
      holFloatIsFinite b = true ∧
        holRatAbs (holFloatToReal b) ≤ holRatAbs (X / 2 ^ 149))
      (X / 2 ^ 149) (fp32OfPat false (fp32Lower X)) := by
  have hf := fp32Directed_finite_bracket hX hmax
  have hl := fp32Lower_le_max hX hmax
  have hm : fp32MaxPat < 2 ^ 31 := by decide
  have hval := fp32OfPat_positive_value (q := fp32Lower X) (by omega)
  have hn0 : (0 : Rat) ≤ ((fp32N (fp32Lower X) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  have hD := fp32_D_pos
  have hv0 : 0 ≤ holFloatToReal (fp32OfPat false (fp32Lower X)) := by rw [hval]; grind
  have hx0 : 0 ≤ X / 2 ^ 149 := by grind
  constructor
  · constructor
    · exact hf.1
    · unfold holRatAbs
      split <;> split <;> grind
  · intro b hb
    have hbbelow : holFloatToReal b ≤ X / 2 ^ 149 := by
      have ha := hb.2
      unfold holRatAbs at ha
      split at ha <;> split at ha <;> grind
    exact (fp32Lower_isClosest hX hmax).2 b ⟨hb.1, hbbelow⟩

/-- All closest below-candidates have the lower bracket's represented value. -/
theorem fp32Lower_closest_value {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) (b : HolFloat 23 8)
    (hb : holIsClosest (fun c : HolFloat 23 8 =>
      holFloatIsFinite c = true ∧ holFloatToReal c ≤ X / 2 ^ 149)
      (X / 2 ^ 149) b) :
    holFloatToReal b = holFloatToReal (fp32OfPat false (fp32Lower X)) := by
  have hc := fp32Lower_isClosest hX hmax
  have hd := hb.2 _ hc.1
  have he := fp32Lower_value_extremal hX hmax b hb.1.2
  have hl := hc.1.2
  have hbval := hb.1.2
  unfold holRatAbs at hd
  split at hd <;> split at hd <;> grind

/-- All closest above-candidates have the upper bracket's represented value. -/
theorem fp32Upper_closest_value {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) (b : HolFloat 23 8)
    (hb : holIsClosest (fun c : HolFloat 23 8 =>
      holFloatIsFinite c = true ∧ X / 2 ^ 149 ≤ holFloatToReal c)
      (X / 2 ^ 149) b) :
    holFloatToReal b = holFloatToReal (fp32OfPat false (fp32Upper X)) := by
  have hc := fp32Upper_isClosest hX hmax
  have hd := hb.2 _ hc.1
  have he := fp32Upper_value_extremal hX hmax b hb.1.2
  have hl := hc.1.2
  have hbval := hb.1.2
  unfold holRatAbs at hd
  split at hd <;> split at hd <;> grind

/-- Toward-zero closest candidates have the same represented value as the lower bracket. -/
theorem fp32Lower_zero_closest_value {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) (b : HolFloat 23 8)
    (hb : holIsClosest (fun c : HolFloat 23 8 =>
      holFloatIsFinite c = true ∧
        holRatAbs (holFloatToReal c) ≤ holRatAbs (X / 2 ^ 149))
      (X / 2 ^ 149) b) :
    holFloatToReal b = holFloatToReal (fp32OfPat false (fp32Lower X)) := by
  have hc := fp32Lower_zero_isClosest hX hmax
  have hd := hb.2 _ hc.1
  have hf := fp32Directed_finite_bracket hX hmax
  have hD := fp32_D_pos
  have hx0 : 0 ≤ X / 2 ^ 149 := by grind
  have hbval : holFloatToReal b ≤ X / 2 ^ 149 := by
    have ha := hb.1.2
    unfold holRatAbs at ha
    split at ha <;> split at ha <;> grind
  have he := fp32Lower_value_extremal hX hmax b hbval
  have hl := hf.2.2.1
  unfold holRatAbs at hd
  split at hd <;> split at hd <;> grind

/-- Equal represented magnitudes have equal patterns when their sign bits agree. -/
theorem fp32_same_sign_value_injective (a b : HolFloat 23 8)
    (hs : a.sign = b.sign) (hv : holFloatToReal a = holFloatToReal b) : a = b := by
  rw [holFloatToReal_fp32, holFloatToReal_fp32, hs] at hv
  have hD := fp32_D_pos
  have hn : ((fp32N (fp32Pat a) : Nat) : Rat) =
      ((fp32N (fp32Pat b) : Nat) : Rat) := by
    by_cases h : b.sign = 1 <;> simp only [h, if_true, if_false] at hv <;> grind
  have hnat : fp32N (fp32Pat a) = fp32N (fp32Pat b) := by exact_mod_cast hn
  have hp : fp32Pat a = fp32Pat b := by
    rcases Nat.lt_trichotomy (fp32Pat a) (fp32Pat b) with h | h | h
    · have := fp32N_strictMono h; omega
    · exact h
    · have := fp32N_strictMono h; omega
  rw [← fp32OfPat_pat a, ← fp32OfPat_pat b, hs, hp]

/-- Finite zero classification depends only on the represented value. -/
theorem fp32_finite_zero_value (f : HolFloat 23 8)
    (hf : holFloatIsFinite f = true) :
    holFloatIsZero f = true ↔ holFloatToReal f = 0 := by
  rw [fp32_isZero_iff f hf]
  rw [holFloatToReal_fp32]
  have hD := fp32_D_pos
  constructor
  · intro hp
    rw [hp]
    have hz : fp32N 0 = 0 := by decide
    rw [hz]
    grind
  · intro hv
    have hn : ((fp32N (fp32Pat f) : Nat) : Rat) = 0 := by
      by_cases hs : f.sign = 1 <;> simp only [hs, if_true, if_false] at hv <;> grind
    have hn' : fp32N (fp32Pat f) = 0 := by exact_mod_cast hn
    exact fp32N_eq_zero.mp hn'

/-- Nonzero equal values force equal signs; the only sign ambiguity is zero. -/
theorem fp32_equal_nonzero_value (a b : HolFloat 23 8)
    (hv : holFloatToReal a = holFloatToReal b)
    (hn : holFloatToReal b ≠ 0) : a = b := by
  apply fp32_same_sign_value_injective a b _ hv
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
  have hD := fp32_D_pos
  have hna : (0 : Rat) ≤ ((fp32N (fp32Pat a) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  have hnb : (0 : Rat) ≤ ((fp32N (fp32Pat b) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  rw [holFloatToReal_fp32, holFloatToReal_fp32] at hv
  rw [holFloatToReal_fp32] at hn
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [ha, hb]
  · simp only [ha, hb] at hv hn
    grind
  · simp only [ha, hb] at hv hn
    grind
  · rw [ha, hb]

/-- Equal finite represented values become equal records after zero-sign selection. -/
theorem fp32_zero_sign_value_eq (a b : HolFloat 23 8)
    (ha : holFloatIsFinite a = true) (hb : holFloatIsFinite b = true)
    (hv : holFloatToReal a = holFloatToReal b) (z : HolFloat 23 8) :
    (if holFloatIsZero a then z else a) =
      (if holFloatIsZero b then z else b) := by
  have hz : holFloatIsZero a = holFloatIsZero b := by
    have he : holFloatIsZero a = true ↔ holFloatIsZero b = true := by
      rw [fp32_finite_zero_value a ha, fp32_finite_zero_value b hb, hv]
    cases hza : holFloatIsZero a <;> cases hzb : holFloatIsZero b <;> simp_all
  rw [hz]
  cases hzb : holFloatIsZero b
  · have hn : holFloatToReal b ≠ 0 := by
      intro h
      have := (fp32_finite_zero_value b hb).2 h
      rw [hzb] at this
      contradiction
    rw [fp32_equal_nonzero_value a b hv hn]
  · rfl

/-- A witnessed closest candidate discharges the choice specification. -/
theorem fp32_closest_spec (s : HolFloat 23 8 → Prop) (x : Rat)
    (a : HolFloat 23 8) (ha : holIsClosest s x a) :
    holIsClosest s x (holClosest s x) := by
  unfold holClosest
  apply (holClosestSuch_spec (fun _ => True) s x _).1
  exact ⟨a, ha, fun _ _ => True.intro⟩

/-- Negation transports any closest predicate whose candidates are transported. -/
theorem fp32_closest_negate (s r : HolFloat 23 8 → Prop) (x : Rat)
    (c : HolFloat 23 8)
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
theorem fp32_below_closest_negate (x : Rat) (c : HolFloat 23 8)
    (hc : holIsClosest (fun a : HolFloat 23 8 =>
      holFloatIsFinite a = true ∧ holFloatToReal a ≤ x) x c) :
    holIsClosest (fun a : HolFloat 23 8 =>
      holFloatIsFinite a = true ∧ -x ≤ holFloatToReal a)
      (-x) (holFloatNegate c) := by
  apply fp32_closest_negate _ _ x c hc
  · intro a ha
    rw [holFloatIsFinite_negate, holFloatToReal_negate]
    exact ⟨ha.1, by grind⟩
  · intro b hb
    rw [holFloatIsFinite_negate, holFloatToReal_negate]
    exact ⟨hb.1, by grind⟩

/-- Negation transports toward-zero's absolute-value candidate set unchanged. -/
theorem fp32_zero_closest_negate (x : Rat) (c : HolFloat 23 8)
    (hc : holIsClosest (fun a : HolFloat 23 8 =>
      holFloatIsFinite a = true ∧ holRatAbs (holFloatToReal a) ≤ holRatAbs x) x c) :
    holIsClosest (fun a : HolFloat 23 8 =>
      holFloatIsFinite a = true ∧ holRatAbs (holFloatToReal a) ≤ holRatAbs (-x))
      (-x) (holFloatNegate c) := by
  apply fp32_closest_negate _ _ x c hc
  · intro a ha
    rw [holFloatIsFinite_negate, holFloatToReal_negate, holRatAbs_neg, holRatAbs_neg]
    exact ha
  · intro b hb
    rw [holFloatIsFinite_negate, holFloatToReal_negate, holRatAbs_neg]
    rw [holRatAbs_neg] at hb
    exact hb

/-- Negation swaps above candidates to below candidates. -/
theorem fp32_above_closest_negate (x : Rat) (c : HolFloat 23 8)
    (hc : holIsClosest (fun a : HolFloat 23 8 =>
      holFloatIsFinite a = true ∧ x ≤ holFloatToReal a) x c) :
    holIsClosest (fun a : HolFloat 23 8 =>
      holFloatIsFinite a = true ∧ holFloatToReal a ≤ -x)
      (-x) (holFloatNegate c) := by
  apply fp32_closest_negate _ _ x c hc
  · intro a ha
    rw [holFloatIsFinite_negate, holFloatToReal_negate]
    exact ⟨ha.1, by grind⟩
  · intro b hb
    rw [holFloatIsFinite_negate, holFloatToReal_negate]
    exact ⟨hb.1, by grind⟩

/-- The three directed cases; nearest-even is proved in the imported module. -/
inductive Fp32Direction where
  | zero | positive | negative
  deriving DecidableEq

/-- Literal directed finite candidate predicates from HOL's three clauses. -/
def fp32DirectedCandidates (d : Fp32Direction) (x : Rat) (b : HolFloat 23 8) : Prop :=
  holFloatIsFinite b = true ∧ match d with
    | .zero => holRatAbs (holFloatToReal b) ≤ holRatAbs x
    | .positive => x ≤ holFloatToReal b
    | .negative => holFloatToReal b ≤ x

/-- Computable positive-domain directed magnitude selection. -/
def fp32DirectedPositive (d : Fp32Direction) (X : Rat) : HolFloat 23 8 :=
  fp32OfPat false (match d with
    | .positive => fp32Upper X
    | .zero | .negative => fp32Lower X)

/-- Positive-domain selection is closest in the exact directed candidate set. -/
theorem fp32DirectedPositive_closest (d : Fp32Direction) {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) :
    holIsClosest (fp32DirectedCandidates d (X / 2 ^ 149))
      (X / 2 ^ 149) (fp32DirectedPositive d X) := by
  cases d
  · exact fp32Lower_zero_isClosest hX hmax
  · exact fp32Upper_isClosest hX hmax
  · exact fp32Lower_isClosest hX hmax

/-- Every directed closest candidate has the computed positive bracket's value. -/
theorem fp32DirectedPositive_closest_value (d : Fp32Direction) {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) (b : HolFloat 23 8)
    (hb : holIsClosest (fp32DirectedCandidates d (X / 2 ^ 149)) (X / 2 ^ 149) b) :
    holFloatToReal b = holFloatToReal (fp32DirectedPositive d X) := by
  cases d
  · exact fp32Lower_zero_closest_value hX hmax b hb
  · exact fp32Upper_closest_value hX hmax b hb
  · exact fp32Lower_closest_value hX hmax b hb

/-- Positive-domain selection is finite, including the largest endpoint. -/
theorem fp32DirectedPositive_finite (d : Fp32Direction) {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) :
    holFloatIsFinite (fp32DirectedPositive d X) = true := by
  have hf := fp32Directed_finite_bracket hX hmax
  cases d
  · exact hf.1
  · exact hf.2.1
  · exact hf.1

/-- Choice-based and computed directed candidates agree after selecting zero's sign. -/
theorem fp32DirectedPositive_choice (d : Fp32Direction) {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) (z : HolFloat 23 8) :
    let c := holClosest (fp32DirectedCandidates d (X / 2 ^ 149)) (X / 2 ^ 149)
    let a := fp32DirectedPositive d X
    (if holFloatIsZero c then z else c) = (if holFloatIsZero a then z else a) := by
  have hc := fp32_closest_spec _ _ _ (fp32DirectedPositive_closest d hX hmax)
  have hv := fp32DirectedPositive_closest_value d hX hmax _ hc
  have hf : holFloatIsFinite
      (holClosest (fp32DirectedCandidates d (X / 2 ^ 149)) (X / 2 ^ 149)) = true := hc.1.1
  exact fp32_zero_sign_value_eq _ _ hf (fp32DirectedPositive_finite d hX hmax) hv z

/-- Negation exchanges upward and downward rounding. -/
def fp32FlipDirection : Fp32Direction → Fp32Direction
  | .zero => .zero
  | .positive => .negative
  | .negative => .positive

/-- Directed candidate sets transform exactly under sign reversal. -/
theorem fp32DirectedCandidates_negate (d : Fp32Direction) (x : Rat) (b : HolFloat 23 8) :
    fp32DirectedCandidates d (-x) (holFloatNegate b) ↔
      fp32DirectedCandidates (fp32FlipDirection d) x b := by
  unfold fp32DirectedCandidates
  rw [holFloatIsFinite_negate, holFloatToReal_negate]
  cases d <;> simp only [fp32FlipDirection]
  · rw [holRatAbs_neg, holRatAbs_neg]
  · constructor <;> intro h <;> exact ⟨h.1, by grind⟩
  · constructor <;> intro h <;> exact ⟨h.1, by grind⟩

/-- The negative-domain computed candidate satisfies the exact closest predicate. -/
theorem fp32DirectedNegative_closest (d : Fp32Direction) {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) :
    holIsClosest (fp32DirectedCandidates d (-(X / 2 ^ 149)))
      (-(X / 2 ^ 149))
      (holFloatNegate (fp32DirectedPositive (fp32FlipDirection d) X)) := by
  apply fp32_closest_negate _ _ _ _
    (fp32DirectedPositive_closest (fp32FlipDirection d) hX hmax)
  · intro a ha
    exact (fp32DirectedCandidates_negate d _ a).2 ha
  · intro b hb
    have h := (fp32DirectedCandidates_negate d (X / 2 ^ 149) (holFloatNegate b)).1
    rw [holFloatNegate_negate] at h
    exact h hb

/-- Negative-domain closest candidates share the computed negative bracket's value. -/
theorem fp32DirectedNegative_closest_value (d : Fp32Direction) {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) (b : HolFloat 23 8)
    (hb : holIsClosest (fp32DirectedCandidates d (-(X / 2 ^ 149)))
      (-(X / 2 ^ 149)) b) :
    holFloatToReal b =
      holFloatToReal (holFloatNegate (fp32DirectedPositive (fp32FlipDirection d) X)) := by
  have hn : holIsClosest (fp32DirectedCandidates (fp32FlipDirection d) (X / 2 ^ 149))
      (X / 2 ^ 149) (holFloatNegate b) := by
    have h := fp32_closest_negate _ _ (-(X / 2 ^ 149)) b hb
      (fun a ha => (fp32DirectedCandidates_negate d (X / 2 ^ 149) (holFloatNegate a)).1
        (by simpa only [holFloatNegate_negate] using ha))
      (fun c hc => (fp32DirectedCandidates_negate d (X / 2 ^ 149) c).2 hc)
    simpa only [Rat.neg_neg] using h
  have hv := fp32DirectedPositive_closest_value (fp32FlipDirection d) hX hmax _ hn
  rw [holFloatToReal_negate] at hv
  rw [holFloatToReal_negate]
  grind

/-- Negative-domain choice agrees with the computed candidate after zero-sign selection. -/
theorem fp32DirectedNegative_choice (d : Fp32Direction) {X : Rat} (hX : 0 ≤ X)
    (hmax : X ≤ ((fp32N fp32MaxPat : Nat) : Rat)) (z : HolFloat 23 8) :
    let c := holClosest (fp32DirectedCandidates d (-(X / 2 ^ 149))) (-(X / 2 ^ 149))
    let a := holFloatNegate (fp32DirectedPositive (fp32FlipDirection d) X)
    (if holFloatIsZero c then z else c) = (if holFloatIsZero a then z else a) := by
  have hc := fp32_closest_spec _ _ _ (fp32DirectedNegative_closest d hX hmax)
  have hv := fp32DirectedNegative_closest_value d hX hmax _ hc
  have hf : holFloatIsFinite
      (holClosest (fp32DirectedCandidates d (-(X / 2 ^ 149))) (-(X / 2 ^ 149))) = true := hc.1.1
  have ha : holFloatIsFinite
      (holFloatNegate (fp32DirectedPositive (fp32FlipDirection d) X)) = true := by
    rw [holFloatIsFinite_negate]
    exact fp32DirectedPositive_finite _ hX hmax
  exact fp32_zero_sign_value_eq _ _ hf ha hv z

/-- Computable signed in-range candidate for the directed modes. -/
def fp32DirectedCandidate (d : Fp32Direction) (x : Rat) : HolFloat 23 8 :=
  if x < 0 then
    holFloatNegate (fp32DirectedPositive (fp32FlipDirection d) (-x * 2 ^ 149))
  else fp32DirectedPositive d (x * 2 ^ 149)

/-- Choice agrees with the computable signed candidate throughout the finite interval. -/
theorem fp32DirectedCandidate_choice (d : Fp32Direction) (x : Rat)
    (hlo : -holFloatLargest 23 8 ≤ x) (hhi : x ≤ holFloatLargest 23 8)
    (z : HolFloat 23 8) :
    let c := holClosest (fp32DirectedCandidates d x) x
    let a := fp32DirectedCandidate d x
    (if holFloatIsZero c then z else c) = (if holFloatIsZero a then z else a) := by
  have hD := fp32_D_pos
  unfold fp32DirectedCandidate
  split
  · next hx =>
      have hX : 0 ≤ -x * 2 ^ 149 := by grind
      have hM : -x * 2 ^ 149 ≤ ((fp32N fp32MaxPat : Nat) : Rat) := by
        rw [← fp32_largest_scaled]
        grind
      have he : -((-x * 2 ^ 149) / 2 ^ 149) = x := by grind
      have h := fp32DirectedNegative_choice d hX hM z
      rw [he] at h
      exact h
  · next hx =>
      have hX : 0 ≤ x * 2 ^ 149 := by grind
      have hM : x * 2 ^ 149 ≤ ((fp32N fp32MaxPat : Nat) : Rat) := by
        rw [← fp32_largest_scaled]
        grind
      have he : (x * 2 ^ 149) / 2 ^ 149 = x := by grind
      have h := fp32DirectedPositive_choice d hX hM z
      rw [he] at h
      exact h

/-- Original rounding mode corresponding to a directed case. -/
def fp32DirectionMode : Fp32Direction → HolRounding
  | .zero => .roundTowardZero
  | .positive => .roundTowardPositive
  | .negative => .roundTowardNegative

/-- Full computable directed rounding, retaining HOL's strict overflow guards. -/
def holFp32DirectedRound (d : Fp32Direction) (toneg : Bool) (x : Rat) : HolFloat 23 8 :=
  let a := if x < -holFloatLargest 23 8 then
      match d with
      | .negative => holFloatMinusInfinity 23 8
      | .zero | .positive => holFloatBottom 23 8
    else if x > holFloatLargest 23 8 then
      match d with
      | .positive => holFloatPlusInfinity 23 8
      | .zero | .negative => holFloatTop 23 8
    else fp32DirectedCandidate d x
  if holFloatIsZero a then
    (if toneg then holFloatMinusZero 23 8 else holFloatPlusZero 23 8)
  else a

/-- Full-domain directed agreement for every rational input and requested zero sign. -/
theorem holFloatRound_directed_fp32 (d : Fp32Direction) (toneg : Bool) (x : Rat) :
    (holFloatRound (fp32DirectionMode d) toneg x : HolFloat 23 8) =
      holFp32DirectedRound d toneg x := by
  have hlow := fp32DirectedCandidate_choice d x
  unfold holFloatRound holFp32DirectedRound
  by_cases hl : x < -holFloatLargest 23 8
  · cases d <;> simp only [fp32DirectionMode, holRound, hl, if_true]
  · by_cases hh : x > holFloatLargest 23 8
    · cases d <;> simp only [fp32DirectionMode, holRound, hl, hh, if_false, if_true]
    · have hlo : -holFloatLargest 23 8 ≤ x := by grind
      have hhi : x ≤ holFloatLargest 23 8 := by grind
      have h := hlow hlo hhi
        (if toneg then holFloatMinusZero 23 8 else holFloatPlusZero 23 8)
      cases d <;> dsimp [fp32DirectionMode, holRound, fp32DirectedCandidates] at h ⊢ <;>
        simp only [hl, hh, if_false] <;> exact h

end Flapjack.Binary32Rounding

namespace Flapjack

/-- Computable binary32 rounding for all four original modes. This is untagged
infrastructure: HOL does not name this algorithm. Agreement below is with the
existing rational rendering; SOUNDNESS item 8 remains an external assumption. -/
def holFp32Round (mode : HolRounding) (toneg : Bool) (x : Rat) : HolFloat 23 8 :=
  match mode with
  | .roundTiesToEven => holFp32RoundTiesToEven toneg x
  | .roundTowardZero => Binary32Rounding.holFp32DirectedRound .zero toneg x
  | .roundTowardPositive => Binary32Rounding.holFp32DirectedRound .positive toneg x
  | .roundTowardNegative => Binary32Rounding.holFp32DirectedRound .negative toneg x

/-- Complete binary32 agreement, with no additional premise, for every mode,
rational argument and requested zero sign. This does not establish cross-HOL
real equality, and therefore carries no original-declaration tag. -/
theorem holFloatRound_fp32 (mode : HolRounding) (toneg : Bool) (x : Rat) :
    (holFloatRound mode toneg x : HolFloat 23 8) = holFp32Round mode toneg x := by
  cases mode
  · exact holFloatRound_rte_fp32 toneg x
  · exact Binary32Rounding.holFloatRound_directed_fp32 .positive toneg x
  · exact Binary32Rounding.holFloatRound_directed_fp32 .negative toneg x
  · exact Binary32Rounding.holFloatRound_directed_fp32 .zero toneg x

end Flapjack
