module

public import Flapjack.Misc.Multiword.Mc.Correct.Mul
public import Flapjack.Misc.Multiword.Mc.DivSimple

@[expose] public section

/-! Correctness of the machine-code-style division by a single word and of
the normalisation-factor computation of HOL's `mc_multiword`. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Flapjack proof of the local HOL lemma `mc_single_div_thm`. -/
theorem mcSingleDiv_thm {width : Nat} [NeZero width] {x2 x1 y : BitVec width} :
    (mcSingleDivPre (x2, x1, y) ↔ x1 < y) ∧
      mcSingleDiv (x2, x1, y) = ((singleDiv x1 x2 y).1, (singleDiv x1 x2 y).2, y) := by
  refine ⟨?_, by rw [mcSingleDiv_def]⟩
  rw [mcSingleDivPre_def]
  simp only [singleDivPre, BitVec.lt_def]
  have hx1 := x1.isLt
  have hx2 := x2.isLt
  constructor
  · rintro ⟨ne, lt⟩
    have hy : 0 < y.toNat := by
      rcases Nat.eq_zero_or_pos y.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) ne
      · exact h
    rw [Nat.div_lt_iff_lt_mul hy] at lt
    by_contra hc
    have : y.toNat * 2 ^ width ≤ x1.toNat * 2 ^ width :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.mul_comm (2 ^ width) y.toNat] at lt
    omega
  · intro h
    have hy : 0 < y.toNat := by omega
    refine ⟨fun e => by rw [e] at h; simp at h, ?_⟩
    rw [Nat.div_lt_iff_lt_mul hy]
    have : (x1.toNat + 1) * 2 ^ width ≤ y.toNat * 2 ^ width :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [Nat.mul_comm (2 ^ width) y.toNat]
    omega

/-- Flapjack proof of the local HOL lemma `mc_simple_div_thm`. -/
theorem mcSimpleDiv_thm {width : Nat} [NeZero width] :
    ∀ (xs xs1 zs zs1 : List (BitVec width)) (r2 r9 : BitVec width)
      (qs : List (BitVec width)) (r : BitVec width) (l : Nat),
      xs.length < 2 ^ width ∧ zs.length = xs.length ∧ xs.length ≤ l ∧
      mwSimpleDiv r2 xs.reverse r9 = (qs, r, true) →
      mcSimpleDivPre (l, r2, r9, BitVec.ofNat width xs.length, xs ++ xs1, zs ++ zs1) ∧
      mcSimpleDiv (l, r2, r9, BitVec.ofNat width xs.length, xs ++ xs1, zs ++ zs1) =
        (l - xs.length, r, r9, 0, xs ++ xs1, qs.reverse ++ zs1) := by
  intro xs
  induction xs using snoc_induction with
  | nil =>
    intro xs1 zs zs1 r2 r9 qs r l ⟨_, hz, _, h⟩
    rw [List.eq_nil_of_length_eq_zero hz]
    simp only [List.reverse_nil, mwSimpleDiv, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨by rw [mcSimpleDivPre_def]; simp, by rw [mcSimpleDiv_def]; simp⟩
  | snoc xs x ih =>
    intro xs1 zs zs1 r2 r9 qs r l ⟨hlt, hz, hle, h⟩
    obtain ⟨zs, z, rfl⟩ : ∃ zs' z, zs = zs' ++ [z] := by
      rcases List.eq_nil_or_concat zs with e | ⟨L, b, e⟩
      · subst e; simp at hz
      · exact ⟨L, b, by simpa using e⟩
    simp only [List.length_append, List.length_singleton] at hlt hz hle ⊢
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      mwSimpleDiv] at h
    rcases hqr : singleDiv r2 x r9 with ⟨q1, r1⟩
    rcases hrest : mwSimpleDiv r1 xs.reverse r9 with ⟨qs', r', c⟩
    simp only [hqr, hrest, Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, rfl, rfl, hc⟩ := h
    obtain ⟨pre, eq⟩ := ih (x :: xs1) zs (q1 :: zs1) r1 r9 qs' r' (l - 1)
      ⟨by omega, by omega, by omega, hrest⟩
    have ne : BitVec.ofNat width (xs.length + 1) ≠ 0 := by
      rw [Ne, ofNat_eq_zero hlt]; omega
    have sub := ofNat_succ_sub_one (width := width) (n := xs.length) hlt
    have tn : (BitVec.ofNat width xs.length).toNat = xs.length := ofNat_toNat_of_lt (by omega)
    have ex : holEl xs.length (xs ++ [x] ++ xs1) = x := by
      simpa using holEl_append_length xs xs1 x
    have sz : (zs ++ [z] ++ zs1).set xs.length q1 = zs ++ q1 :: zs1 := by
      rw [show xs.length = zs.length by omega]; simp
    rw [mcSimpleDivPre_def, mcSimpleDiv_def]
    simp only [ne, if_false, sub, tn, ex, mcSingleDiv_thm.2, mcSingleDiv_thm.1, hqr, sz]
    simp only [List.append_assoc, List.singleton_append] at pre eq ⊢
    refine ⟨⟨pre, ⟨⟨by simp, hc⟩, by simp; omega⟩, by omega⟩, ?_⟩
    rw [eq]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    congr 1; omega

/-- Flapjack proof of the local HOL lemma `mc_simple_div1_thm`. -/
theorem mcSimpleDiv1_thm {width : Nat} [NeZero width] :
    ∀ (zs zs1 : List (BitVec width)) (r2 r9 : BitVec width)
      (qs : List (BitVec width)) (r : BitVec width) (l : Nat),
      zs.length < 2 ^ width ∧ zs.length ≤ l ∧
      mwSimpleDiv r2 zs.reverse r9 = (qs, r, true) →
      mcSimpleDiv1Pre (l, r2, r9, BitVec.ofNat width zs.length, zs ++ zs1) ∧
      mcSimpleDiv1 (l, r2, r9, BitVec.ofNat width zs.length, zs ++ zs1) =
        (l - zs.length, r, r9, 0, qs.reverse ++ zs1) := by
  intro zs
  induction zs using snoc_induction with
  | nil =>
    intro zs1 r2 r9 qs r l ⟨_, _, h⟩
    simp only [List.reverse_nil, mwSimpleDiv, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨by rw [mcSimpleDiv1Pre_def]; simp, by rw [mcSimpleDiv1_def]; simp⟩
  | snoc zs x ih =>
    intro zs1 r2 r9 qs r l ⟨hlt, hle, h⟩
    simp only [List.length_append, List.length_singleton] at hlt hle ⊢
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      mwSimpleDiv] at h
    rcases hqr : singleDiv r2 x r9 with ⟨q1, r1⟩
    rcases hrest : mwSimpleDiv r1 zs.reverse r9 with ⟨qs', r', c⟩
    simp only [hqr, hrest, Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, rfl, rfl, hc⟩ := h
    obtain ⟨pre, eq⟩ := ih (q1 :: zs1) r1 r9 qs' r' (l - 1) ⟨by omega, by omega, hrest⟩
    have ne : BitVec.ofNat width (zs.length + 1) ≠ 0 := by
      rw [Ne, ofNat_eq_zero hlt]; omega
    have sub := ofNat_succ_sub_one (width := width) (n := zs.length) hlt
    have tn : (BitVec.ofNat width zs.length).toNat = zs.length := ofNat_toNat_of_lt (by omega)
    have ex : holEl zs.length (zs ++ [x] ++ zs1) = x := by
      simpa using holEl_append_length zs zs1 x
    have sz : (zs ++ [x] ++ zs1).set zs.length q1 = zs ++ q1 :: zs1 := by simp
    rw [mcSimpleDiv1Pre_def, mcSimpleDiv1_def]
    simp only [ne, if_false, sub, tn, ex, mcSingleDiv_thm.2, mcSingleDiv_thm.1, hqr, sz]
    refine ⟨⟨pre, ⟨by simp, hc⟩, by omega⟩, ?_⟩
    rw [eq]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    congr 1; omega

/-- The general form of the local HOL lemma `mc_calc_d_thm`, by induction on
the remaining doubling budget `n` (Flapjack proof). -/
theorem mcCalcD_thm_gen {width : Nat} [NeZero width] :
    ∀ (n : Nat) (v1 d : BitVec width) (l : Nat),
      v1 ≠ 0 ∧ 2 ^ width ≤ v1.toNat * 2 ^ n ∧ n ≤ l →
      ∃ l2, mcCalcDPre (l, v1, d) ∧ mcCalcD (l, v1, d) = (l2, calcD (v1, d)) ∧ l ≤ l2 + n := by
  intro n
  induction n with
  | zero =>
    intro v1 d l ⟨_, h, _⟩
    have := v1.isLt
    simp at h; omega
  | succ n ih =>
    intro v1 d l ⟨ne, h, hl⟩
    have pos := Nat.pos_of_ne_zero (NeZero.ne width)
    have slt : v1.slt 0 = v1.msb := BitVec.slt_zero_eq_msb
    rw [mcCalcDPre_def, mcCalcD_def, calcD]
    by_cases hm : v1.msb = true
    · simp only [slt, hm, if_true, or_true]
      exact ⟨l, trivial, rfl, by omega⟩
    · have hf : v1.msb = false := by simpa using hm
      have hw : 2 ^ width = 2 * 2 ^ (width - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      have lt : v1.toNat < 2 ^ (width - 1) := by
        rw [BitVec.msb_eq_decide] at hf; simpa using hf
      have dbl : (v1 + v1).toNat = 2 * v1.toNat := by
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
      have e2 : v1 + v1 = v1 * 2 := BitVec.mul_two.symm
      have e2d : d + d = d * 2 := BitVec.mul_two.symm
      have ne2 : v1 + v1 ≠ 0 := by
        intro z; have := congrArg BitVec.toNat z; rw [dbl] at this
        have : 0 < v1.toNat := Nat.pos_of_ne_zero fun e =>
          ne (BitVec.eq_of_toNat_eq (by simpa using e))
        simp at *; omega
      obtain ⟨l2, pre, eq, bound⟩ := ih (v1 + v1) (d + d) (l - 1)
        ⟨ne2, by
          rw [dbl]
          have : v1.toNat * 2 ^ (n + 1) = 2 * v1.toNat * 2 ^ n := by ring
          omega, by omega⟩
      simp only [slt, hf, Bool.false_eq_true, if_false, ne, false_or]
      refine ⟨l2, ⟨pre, by omega⟩, ?_, by omega⟩
      rw [eq, e2, e2d]

/-- Flapjack proof of the local HOL lemma `mc_calc_d_thm`. -/
theorem mcCalcD_thm {width : Nat} [NeZero width] {v1 d : BitVec width} {l : Nat} :
    v1 ≠ 0 ∧ width ≤ l →
    ∃ l2, mcCalcDPre (l, v1, d) ∧ mcCalcD (l, v1, d) = (l2, calcD (v1, d)) ∧ l ≤ l2 + width := by
  rintro ⟨ne, hl⟩
  refine mcCalcD_thm_gen width v1 d l ⟨ne, ?_, hl⟩
  have : 0 < v1.toNat := Nat.pos_of_ne_zero fun e =>
    ne (BitVec.eq_of_toNat_eq (by simpa using e))
  calc 2 ^ width = 1 * 2 ^ width := (Nat.one_mul _).symm
    _ ≤ v1.toNat * 2 ^ width := Nat.mul_le_mul_right _ this

end Flapjack.Misc.Multiword
