module

public import Flapjack.Misc.Multiword.DivLemmas
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The normalisation factor of Knuth's division algorithm. -/
namespace Flapjack.Misc.Multiword
open Flapjack

private theorem double_toNat {width : Nat} [NeZero width] (v : BitVec width) (h : v.msb = false) :
    (v * 2).toNat = 2 * v.toNat := by
  have pos := Nat.pos_of_ne_zero (NeZero.ne width)
  have hw : 2 ^ width = 2 * 2 ^ (width - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have lt : v.toNat < 2 ^ (width - 1) := by
    rw [BitVec.msb_eq_decide] at h
    simpa using h
  have two_toNat : (2 : BitVec width).toNat = 2 % 2 ^ width := by simp
  rw [BitVec.toNat_mul, two_toNat]
  by_cases w1 : width = 1
  · subst w1; simp at lt; simp [lt]
  · have two : 2 % 2 ^ width = 2 := Nat.mod_eq_of_lt (by
      have : 2 ≤ 2 ^ (width - 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (width - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega)
    rw [two, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

/-- Double both components until the first one is zero or has its top bit set. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "calc_d_def"
  (words_as_type_indexed_bitvec)]
def calcD {width : Nat} [NeZero width] : BitVec width × BitVec width → BitVec width
  | (v1, d) => if v1 = 0 ∨ v1.msb then d else calcD (v1 * 2, d * 2)
termination_by p => 2 ^ width - p.1.toNat
decreasing_by
  rename_i h
  simp only [not_or, Bool.not_eq_true] at h
  have := double_toNat v1 h.2
  have pos : 0 < v1.toNat := Nat.pos_of_ne_zero fun e => h.1 (BitVec.eq_of_toNat_eq (by simpa using e))
  have := (v1 * 2).isLt
  omega

/-- The top bit is set exactly in the upper half of the word range. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "d_word_msb"
  (words_as_type_indexed_bitvec)]
theorem d_word_msb {width : Nat} [NeZero width] :
    ∀ a : BitVec width, a.msb = true ↔ 2 ^ width / 2 ≤ a.toNat := by
  intro a
  have pos := Nat.pos_of_ne_zero (NeZero.ne width)
  have hw : 2 ^ width / 2 = 2 ^ (width - 1) := by
    rw [show width = width - 1 + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
    simp
  rw [hw, BitVec.msb_eq_decide]
  simp

/-- The normalisation factor scales linearly with its seed. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "d_lemma1"
  (words_as_type_indexed_bitvec)]
theorem d_lemma1 {width : Nat} [NeZero width] :
    ∀ (v1 d x : BitVec width), calcD ((v1, d).1, (v1, d).2 * x) = calcD (v1, d) * x := by
  intro v1 d x
  simp only
  refine calcD.induct (motive := fun p => calcD (p.1, p.2 * x) = calcD p * x) ?_ ?_ (v1, d)
  · intro v1 d h
    simp only
    rw [calcD, if_pos h, calcD, if_pos h]
  · intro v1 d h ih
    simp only at ih ⊢
    conv_lhs => rw [calcD, if_neg h]
    conv_rhs => rw [calcD, if_neg h]
    rw [← ih]
    congr 2
    rw [BitVec.mul_assoc, BitVec.mul_comm x 2, ← BitVec.mul_assoc]

private theorem calcD_double {width : Nat} [NeZero width] (v1 : BitVec width) :
    calcD (v1, (2 : BitVec width)) = calcD (v1, 1) * 2 := by
  have := d_lemma1 v1 1 2
  simpa using this

private theorem calcD_props {width : Nat} [NeZero width] :
    ∀ v1 : BitVec width,
      (calcD (v1, 1)).toNat * v1.toNat < 2 ^ width ∧
      (∃ n, (calcD (v1, 1)).toNat = 2 ^ n) ∧
      (v1 ≠ 0 → 2 ^ width / 2 ≤ (calcD (v1, 1) * v1).toNat) := by
  intro v1
  have pos := Nat.pos_of_ne_zero (NeZero.ne width)
  have one_lt : 1 < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  have oneNat : (1 : BitVec width).toNat = 1 := by simp [Nat.mod_eq_of_lt one_lt]
  refine calcD.induct (motive := fun p =>
      (calcD (p.1, 1)).toNat * p.1.toNat < 2 ^ width ∧
      (∃ n, (calcD (p.1, 1)).toNat = 2 ^ n) ∧
      (p.1 ≠ 0 → 2 ^ width / 2 ≤ (calcD (p.1, 1) * p.1).toNat)) ?_ ?_ (v1, 1)
  · intro v1 d h
    simp only
    rw [calcD, if_pos h, oneNat, Nat.one_mul]
    refine ⟨v1.isLt, ⟨0, rfl⟩, fun ne => ?_⟩
    rcases h with h | h
    · exact absurd h ne
    · simpa using (d_word_msb v1).mp h
  · intro v1 d h0 ih
    simp only at ih ⊢
    have h := h0
    simp only [not_or, Bool.not_eq_true] at h
    have msbLt : v1.toNat < 2 ^ (width - 1) := by
      have h2 := h.2
      rw [BitVec.msb_eq_decide] at h2
      simpa using h2
    have dbl := double_toNat v1 h.2
    have ne2 : v1 * 2 ≠ 0 := by
      intro e
      have z : (v1 * 2).toNat = 0 := by rw [e]; simp
      have : 0 < v1.toNat := Nat.pos_of_ne_zero fun z => h.1 (BitVec.eq_of_toNat_eq (by simpa using z))
      omega
    obtain ⟨lt3, ⟨n, pow⟩, lower⟩ := ih
    have h12 : (1 : BitVec width) * 2 = 2 := by simp
    rw [calcD, if_neg h0, h12, calcD_double]
    have c2 : (calcD (v1 * 2, (1 : BitVec width)) * 2).toNat = 2 * (calcD (v1 * 2, 1)).toNat := by
      have := lt3
      rw [dbl] at this
      have v1pos : 0 < v1.toNat := Nat.pos_of_ne_zero fun z => h.1 (BitVec.eq_of_toNat_eq (by simpa using z))
      have two_toNat : (2 : BitVec width).toNat = 2 % 2 ^ width := by simp
      rw [BitVec.toNat_mul, two_toNat]
      by_cases w1 : width = 1
      · subst w1; simp at msbLt; omega
      · have two : 2 % 2 ^ width = 2 := Nat.mod_eq_of_lt (by
          have : 2 ^ 1 ≤ 2 ^ (width - 1) := Nat.pow_le_pow_right (by decide) (by omega)
          have hw : 2 ^ width = 2 * 2 ^ (width - 1) := by rw [← Nat.pow_succ']; congr 1; omega
          simp at this; omega)
        rw [two, Nat.mod_eq_of_lt]
        · rw [Nat.mul_comm]
        · calc (calcD (v1 * 2, 1)).toNat * 2 ≤ (calcD (v1 * 2, 1)).toNat * (2 * v1.toNat) :=
                Nat.mul_le_mul_left _ (by omega)
            _ < 2 ^ width := this
    refine ⟨?_, ⟨n + 1, by rw [c2, pow, Nat.pow_succ, Nat.mul_comm]⟩, fun _ => ?_⟩
    · rw [c2]; rw [dbl] at lt3
      calc 2 * (calcD (v1 * 2, 1)).toNat * v1.toNat
          = (calcD (v1 * 2, 1)).toNat * (2 * v1.toNat) := by ring
        _ < 2 ^ width := lt3
    · have := lower ne2
      rwa [BitVec.mul_assoc, BitVec.mul_comm 2 v1]

/-- The normalised leading digit is at least half the word range. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "d_lemma2"
  (words_as_type_indexed_bitvec)]
theorem d_lemma2 {width : Nat} [NeZero width] :
    ∀ (v1 d : BitVec width), (v1, d).1 ≠ 0 →
      2 ^ width / 2 ≤ (calcD ((v1, d).1, 1) * (v1, d).1).toNat := by
  intro v1 d ne
  exact (calcD_props v1).2.2 ne

/-- The normalisation factor of a nonzero leading digit is nonzero. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "d_lemma2_bis"
  (words_as_type_indexed_bitvec)]
theorem d_lemma2_bis {width : Nat} [NeZero width] :
    ∀ (v1 d : BitVec width), (v1, d).1 ≠ 0 → calcD ((v1, d).1, 1) ≠ 0 := by
  intro v1 d ne
  obtain ⟨n, pow⟩ := (calcD_props v1).2.1
  intro z
  rw [z] at pow
  simp at pow
  exact absurd pow.symm (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos n))

/-- Normalisation does not overflow the leading digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "d_lemma3"
  (words_as_type_indexed_bitvec)]
theorem d_lemma3 {width : Nat} [NeZero width] :
    ∀ (v1 d : BitVec width), (calcD ((v1, d).1, 1)).toNat * ((v1, d).1).toNat < 2 ^ width := by
  intro v1 d
  exact (calcD_props v1).1

/-- The normalisation factor is a power of two. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "d_lemma4"
  (words_as_type_indexed_bitvec)]
theorem d_lemma4 {width : Nat} [NeZero width] :
    ∀ (v1 d : BitVec width), ∃ n, (calcD ((v1, d).1, 1)).toNat = 2 ^ n := by
  intro v1 d
  exact (calcD_props v1).2.1

/-- A nontrivial normalisation factor leaves room for one more unit of the digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "d_lemma5"
  (words_as_type_indexed_bitvec)]
theorem d_lemma5 {width : Nat} [NeZero width] :
    ∀ (v1 d : BitVec width), 2 ≤ (calcD ((v1, d).1, 1)).toNat →
      (calcD ((v1, d).1, 1)).toNat * (((v1, d).1).toNat + 1) ≤ 2 ^ width := by
  intro v1 d two
  simp only at two ⊢
  obtain ⟨lt, ⟨n, pow⟩, _⟩ := calcD_props v1
  rw [pow] at lt two ⊢
  have npos : 1 ≤ n := by
    rcases n with _ | n
    · simp at two
    · omega
  have v1pos : 0 < v1.toNat := by
    rcases Nat.eq_zero_or_pos v1.toNat with z | z
    · exfalso
      have : v1 = 0 := BitVec.eq_of_toNat_eq (by simpa using z)
      subst this
      rw [calcD, if_pos (Or.inl rfl)] at pow
      have h1 : (1 : BitVec width).toNat = 1 :=
        by simp [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (NeZero.ne width))]
      rw [h1] at pow
      have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) npos
      omega
    · exact z
  have nle : n ≤ width := by
    have : 2 ^ n < 2 ^ width := by
      calc 2 ^ n ≤ 2 ^ n * v1.toNat := Nat.le_mul_of_pos_right _ v1pos
        _ < 2 ^ width := lt
    exact Nat.le_of_lt ((Nat.pow_lt_pow_iff_right (by decide)).mp this)
  have split : 2 ^ width = 2 ^ n * 2 ^ (width - n) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [split] at lt ⊢
  have := Nat.lt_of_mul_lt_mul_left lt
  exact Nat.mul_le_mul_left _ this

end Flapjack.Misc.Multiword
