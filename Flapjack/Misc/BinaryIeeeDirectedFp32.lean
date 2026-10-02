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

end Flapjack.Binary32Rounding
