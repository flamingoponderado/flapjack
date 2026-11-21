module

public import Flapjack.Misc.Multiword.Mc.Correct.DivSimple
public import Flapjack.Misc.Multiword.Mc.Div

@[expose] public section

/-! Correctness of the machine-code-style trial quotient digit computation of
HOL's `mc_multiword`. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Flapjack proof of the local HOL lemma `mc_single_mul_thm`. -/
theorem mcSingleMul_thm {width : Nat} [NeZero width] {p k q : BitVec width} :
    mcSingleMulPre (p, k, q) ∧
      mcSingleMul (p, k, q) = ((singleMulAdd p q k 0).1, k, (singleMulAdd p q k 0).2) := by
  refine ⟨by rw [mcSingleMulPre_def]; trivial, ?_⟩
  rw [mcSingleMul_def]
  have bF : (0 : BitVec width) = b2w false := by simp [b2w, b2n]
  have zw : ∀ x y : BitVec width, singleAddWord x y 0 =
      ((singleAdd x y false).1, b2w (singleAdd x y false).2) := by
    intro x y; rw [bF, singleAddWord_b2w]
  have mul := singleMul_value p q 0
  rcases ha : singleMul p q 0 with ⟨a, hi⟩
  rw [ha] at mul
  dsimp only at mul ⊢
  simp only [zw, singleAddWord_b2w]
  rcases hb : singleAdd a k false with ⟨r0b, ca⟩
  have a1 := singleAdd_thm a k r0b false ca hb
  rcases hc : singleAdd hi 0 ca with ⟨r2b, d1⟩
  have a2 := singleAdd_thm hi 0 r2b ca d1 hc
  rcases hs : singleMulAdd p q k 0 with ⟨x1, x2⟩
  have spec := singleMulAdd_thm p q k 0 x1 x2 hs
  have hw : 0 < 2 ^ width := Nat.two_pow_pos _
  have hp := p.isLt
  have hq := q.isLt
  have hk := k.isLt
  have prod : p.toNat * q.toNat ≤ (2 ^ width - 1) * (2 ^ width - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have sq : (2 ^ width - 1) * (2 ^ width - 1) + 2 * (2 ^ width - 1) < 2 ^ width * 2 ^ width := by
    obtain ⟨a, ha⟩ : ∃ a, 2 ^ width = a + 1 := ⟨2 ^ width - 1, by omega⟩
    rw [ha, Nat.add_sub_cancel]
    have : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
    omega
  have z0 : (0 : BitVec width).toNat = 0 := by simp
  rw [z0, Nat.add_zero] at a2 mul spec
  have s2 := congrArg (2 ^ width * ·) a2
  simp only [Nat.mul_add, ← Nat.mul_assoc] at s2
  have total : r0b.toNat + 2 ^ width * r2b.toNat = x1.toNat + 2 ^ width * x2.toNat := by
    cases ca <;> cases d1 <;>
      simp only [b2n, Nat.mul_one, Nat.mul_zero, Nat.add_zero] at a1 a2 s2 <;> omega
  have u1 := two_digits_unique r0b.isLt total
  have u2 := two_digits_unique (b := x2.toNat) x1.isLt rfl
  have e1 : r0b = x1 := BitVec.eq_of_toNat_eq (by rw [u1.1, ← u2.1])
  have e2 : r2b = x2 := BitVec.eq_of_toNat_eq (by
    have := u1.2; rw [this]; exact u2.2.symm)
  rw [e1, e2]

/-- `k2mw 2 0` is two zero digits (Flapjack helper). -/
theorem k2mw_two_zero {width : Nat} [NeZero width] :
    (k2mw 2 0 : List (BitVec width)) = [0, 0] := by
  simp [k2mw]

/-- Flapjack proof of the local HOL lemma `mc_mul_by_single2_thm`. -/
theorem mcMulBySingle2_thm {width : Nat} [NeZero width] :
    ∀ r6 r7 r8 : BitVec width, ∃ r1 r2 r3,
      mcMulBySingle2Pre (r6, r7, r8) ∧
      mcMulBySingle2 (r6, r7, r8) = (r1, r2, r3, r6, r7, r8) ∧
      mwMulBySingle r6 [r7, r8] = [r1, r2, r3] := by
  intro r6 r7 r8
  refine ⟨(singleMulAdd r6 r7 0 0).1, (singleMulAdd r6 r8 (singleMulAdd r6 r7 0 0).2 0).1,
    (singleMulAdd r6 r8 (singleMulAdd r6 r7 0 0).2 0).2, ?_, ?_, ?_⟩
  · rw [mcMulBySingle2Pre_def]
    simp only [mcSingleMul_thm.2]
    exact ⟨mcSingleMul_thm.1, mcSingleMul_thm.1⟩
  · rw [mcMulBySingle2_def]
    simp only [mcSingleMul_thm.2]
  · simp only [mwMulBySingle, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
      k2mw_two_zero, mwMulPass, holHd, List.tail_cons]

/-- `mw_cmp` of two three-digit numbers, most significant digit first
(Flapjack helper). -/
theorem mwCmp_three {width : Nat} [NeZero width] (a0 a1 a2 b0 b1 b2 : BitVec width) :
    mwCmp [a0, a1, a2] [b0, b1, b2] =
      if a2 = b2 then
        if a1 = b1 then
          if a0 = b0 then none else some (decide (a0 < b0))
        else some (decide (a1 < b1))
      else some (decide (a2 < b2)) := by
  rw [mwCmp]
  simp only [reduceCtorEq, if_false, holLast, List.dropLast_cons_cons, List.dropLast_singleton]
  split
  · rw [mwCmp]
    simp only [reduceCtorEq, if_false, holLast, List.dropLast_cons_cons, List.dropLast_singleton]
    split
    · rw [mwCmp]
      simp only [reduceCtorEq, if_false, holLast, List.dropLast_singleton]
      split
      · rw [mwCmp]; simp
      · rfl
    · rfl
  · rfl

/-- `mw_cmp` of two two-digit numbers (Flapjack helper). -/
theorem mwCmp_two {width : Nat} [NeZero width] (a0 a1 b0 b1 : BitVec width) :
    mwCmp [a0, a1] [b0, b1] =
      if a1 = b1 then
        if a0 = b0 then none else some (decide (a0 < b0))
      else some (decide (a1 < b1)) := by
  rw [mwCmp]
  simp only [reduceCtorEq, if_false, holLast, List.dropLast_cons_cons, List.dropLast_singleton]
  split
  · rw [mwCmp]
    simp only [reduceCtorEq, if_false, holLast, List.dropLast_singleton]
    split
    · rw [mwCmp]; simp
    · rfl
  · rfl

/-- Flapjack proof of the local HOL lemma `mc_cmp3_thm`. -/
theorem mcCmp3_thm {width : Nat} [NeZero width] {r1 r2 r3 r9 r10 r11 : BitVec width} :
    mcCmp3Pre (r1, r2, r3, r9, r10, r11) ∧
      mcCmp3 (r1, r2, r3, r9, r10, r11) =
        (if mwCmp [r9, r10, r11] [r1, r2, r3] = some true then 1 else 0,
          r1, r2, r3, r9, r10, r11) := by
  refine ⟨by rw [mcCmp3Pre_def]; split_ifs <;> trivial, ?_⟩
  rw [mcCmp3_def, mwCmp_three]
  by_cases h3 : r11 = r3
  · subst h3
    by_cases h2 : r10 = r2
    · subst h2
      by_cases h1 : r9 = r1
      · subst h1; simp
      · by_cases h : r9 < r1 <;> simp [h1, Ne.symm h1, h]
    · by_cases h : r10 < r2 <;> simp [h2, Ne.symm h2, h]
  · by_cases h : r11 < r3 <;> simp [h3, Ne.symm h3, h]

/-- Flapjack proof of the local HOL lemma `mc_cmp_mul2_thm`. -/
theorem mcCmpMul2_thm {width : Nat} [NeZero width] {r6 r7 r8 r9 r10 r11 : BitVec width} :
    mcCmpMul2Pre (r6, r7, r8, r9, r10, r11) ∧
      mcCmpMul2 (r6, r7, r8, r9, r10, r11) =
        (if mwCmp [r9, r10, r11] (mwMulBySingle r6 [r7, r8]) = some true then 1 else 0,
          r6, r7, r8, r9, r10, r11) := by
  obtain ⟨r1, r2, r3, pre, eq, val⟩ := mcMulBySingle2_thm r6 r7 r8
  refine ⟨?_, ?_⟩
  · rw [mcCmpMul2Pre_def]; exact pre
  · rw [mcCmpMul2_def]; simp only [eq, mcCmp3_thm.2, val]

/-- Flapjack proof of the local HOL lemma `mc_sub1_thm`. -/
theorem mcSub1_thm {width : Nat} [NeZero width] :
    ∀ r6 : BitVec width, mcSub1Pre r6 ∧ mcSub1 r6 = BitVec.ofNat width (r6.toNat - 1) := by
  intro r6
  refine ⟨by rw [mcSub1Pre_def]; split <;> trivial, ?_⟩
  rw [mcSub1_def]
  split
  · rename_i h; subst h; simp
  · rename_i h
    have : r6.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    apply BitVec.eq_of_toNat_eq
    have h1 : (1 : Nat) < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp [Nat.mod_eq_of_lt h1]; omega)]
    simp [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) r6.isLt), Nat.mod_eq_of_lt h1]

/-- Flapjack proof of the local HOL lemma `mc_cmp2_thm`. -/
theorem mcCmp2_thm {width : Nat} [NeZero width] {r0 r2 r10 r11 : BitVec width} :
    mcCmp2Pre (r0, r2, r10, r11) ∧
      mcCmp2 (r0, r2, r10, r11) =
        (r0, if mwCmp [r10, r11] [r0, r2] = some true then 1 else 0, r2, r10, r11) := by
  refine ⟨by rw [mcCmp2Pre_def]; split_ifs <;> trivial, ?_⟩
  rw [mcCmp2_def, mwCmp_two]
  by_cases h2 : r11 = r2
  · subst h2
    by_cases h1 : r10 = r0
    · subst h1; simp
    · by_cases h : r10 < r0 <;> simp [h1, Ne.symm h1, h]
  · by_cases h : r11 < r2 <;> simp [h2, Ne.symm h2, h]

/-- Flapjack proof of the local HOL lemma `single_mul_thm`. -/
theorem singleMulAdd_zero_zero {width : Nat} [NeZero width] (x y : BitVec width) :
    singleMulAdd x y 0 0 = singleMul x y 0 := by
  have h1 : (1 : Nat) < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  rcases h : singleMul x y 0 with ⟨a, b⟩
  simp only [singleMulAdd, h, mwAdd, singleAdd, holHd, List.tail_cons, b2w, b2n]
  have ha := a.isLt
  have hb := b.isLt
  simp [Nat.not_le.mpr ha]

/-- Flapjack proof of the local HOL lemma `mw_add_0_1`. -/
theorem mwAdd_0_1 {width : Nat} [NeZero width] (r0 r2 : BitVec width) :
    (mwAdd [r0, r2] [0, 1] false).1 = [r0, r2 + 1] := by
  have ha := r0.isLt
  simp [mwAdd, singleAdd, holHd, b2w, b2n, Nat.not_le.mpr ha]

/-- The trial-digit test cannot fail at a zero digit (Flapjack helper). -/
theorem mwCmp_mulBySingle_zero' {width : Nat} [NeZero width] (u1 u2 u3 v1 v2 : BitVec width) :
    mwCmp [u3, u2, u1] (mwMulBySingle 0 [v2, v1]) ≠ some true := by
  have ⟨val, len⟩ := mwMulBySingle_lemma (0 : BitVec width) [v2, v1]
  rw [mwCmpThm _ _ (by rw [len]; rfl), val]
  simp

/-- Flapjack proof of the local HOL lemma `mc_div_test_lemma`. -/
theorem mcDivTest_lemma {width : Nat} [NeZero width] :
    ∀ (q u1 u2 u3 v1 v2 : BitVec width) (l : Nat), q.toNat ≤ l →
      ∃ l2, mcDivTestPre (l, q, v2, v1, u3, u2, u1) ∧
        mcDivTest (l, q, v2, v1, u3, u2, u1) =
          (l2, mwDivTest q u1 u2 u3 v1 v2, v2, v1, u3, u2, u1) ∧
        l ≤ l2 + q.toNat := by
  intro q u1 u2 u3 v1 v2
  induction h : q.toNat using Nat.strong_induction_on generalizing q with
  | _ n ih =>
    intro l hl
    rw [mcDivTestPre_def, mcDivTest_def, mwDivTest]
    simp only [mcCmpMul2_thm.2]
    by_cases hc : mwCmp [u3, u2, u1] (mwMulBySingle q [v2, v1]) = some true
    · have nz : q.toNat ≠ 0 := by
        intro z
        have : q = 0 := BitVec.eq_of_toNat_eq (by simpa using z)
        subst this
        exact mwCmp_mulBySingle_zero' u1 u2 u3 v1 v2 hc
      have ne1 : (1 : BitVec width) ≠ 0 := by simp [NeZero.ne]
      have p := (mcSub1_thm q).2
      have ptn : (BitVec.ofNat width (q.toNat - 1)).toNat = q.toNat - 1 :=
        ofNat_toNat_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) q.isLt)
      simp only [hc, if_true, ne1, if_false, p, mcSingleMulAdd_thm.2, mcCmp2_thm.2,
        singleMulAdd_zero_zero, mwAdd_0_1]
      by_cases hc2 : mwCmp [u2, u1] [(singleMul (BitVec.ofNat width (q.toNat - 1)) v1 0).1,
          (singleMul (BitVec.ofNat width (q.toNat - 1)) v1 0).2 + 1] = some true
      · obtain ⟨l2, pre, eq, bound⟩ :=
          ih (q.toNat - 1) (by omega) (BitVec.ofNat width (q.toNat - 1)) ptn (l - 1)
            (by omega)
        simp only [hc2, if_true, ne1, if_false]
        exact ⟨l2, ⟨pre, ⟨mcCmpMul2_thm.1, mcSingleMulAdd_thm.1⟩, by omega⟩, eq, by omega⟩
      · simp only [hc2, if_false, if_true]
        exact ⟨l, ⟨mcCmpMul2_thm.1, mcSingleMulAdd_thm.1⟩, rfl, by omega⟩
    · simp only [hc, if_false, if_true]
      exact ⟨l, mcCmpMul2_thm.1, rfl, by omega⟩

/-- Flapjack proof of the local HOL lemma `mc_div_test_thm`. -/
theorem mcDivTest_thm {width : Nat} [NeZero width] :
    ∀ (q u1 u2 u3 v1 v2 : BitVec width) (l : Nat), 2 ^ width ≤ l →
      ∃ l2, mcDivTestPre (l, q, v2, v1, u3, u2, u1) ∧
        mcDivTest (l, q, v2, v1, u3, u2, u1) =
          (l2, mwDivTest q u1 u2 u3 v1 v2, v2, v1, u3, u2, u1) ∧
        l ≤ l2 + 2 ^ width := by
  intro q u1 u2 u3 v1 v2 l hl
  obtain ⟨l2, pre, eq, bound⟩ := mcDivTest_lemma q u1 u2 u3 v1 v2 l (by have := q.isLt; omega)
  exact ⟨l2, pre, eq, by have := q.isLt; omega⟩

/-- Flapjack proof of the local HOL lemma `mc_div_r1_thm`. -/
theorem mcDivR1_thm {width : Nat} [NeZero width] {r0 r1 r2 : BitVec width} :
    mcDivR1 (r0, r1, r2) =
      if r2 < r1 then ((singleDiv r2 r0 r1).1, r1, (singleDiv r2 r0 r1).2)
      else (~~~0, r1, r2) := by
  rw [mcDivR1_def]

/-- Flapjack proof of the local HOL lemma `mc_div_guess_thm`. -/
theorem mcDivGuess_thm {width : Nat} [NeZero width] {us vs : List (BitVec width)} {l : Nat} :
    ∀ u1 u2 u3 v1 v2 : BitVec width, 2 ^ width + 1 ≤ l →
      ∃ l2, (mcDivGuessPre (l, v2, v1, u3, u2, u1) ↔ (u1 < v1 → v1 ≠ 0)) ∧
        mcDivGuess (l, v2, v1, u3, u2, u1) =
          (l2, mwDivGuess (u1 :: u2 :: u3 :: us) (v1 :: v2 :: vs), v2, v1, u3, u2, u1) ∧
        l ≤ l2 + 2 ^ width + 1 := by
  intro u1 u2 u3 v1 v2 hl
  have hnot : (~~~(0 : BitVec width)) = BitVec.ofNat width (2 ^ width - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp
  by_cases hlt : u1 < v1
  · obtain ⟨l2, pre, eq, bound⟩ :=
      mcDivTest_thm (singleDiv u1 u2 v1).1 u1 u2 u3 v1 v2 (l - 1) (by omega)
    refine ⟨l2, ?_, ?_, by omega⟩
    · rw [mcDivGuessPre_def]
      simp only [mcDivR1_thm, hlt, if_true]
      rw [mcDivR1Pre_def]
      simp only [hlt, if_true]
      have := (mcSingleDiv_thm (x2 := u2) (x1 := u1) (y := v1)).1
      rw [mcSingleDivPre_def] at this
      simp only at this
      constructor
      · intro _ _ e; subst e; simp [BitVec.lt_def] at hlt
      · intro _; exact ⟨this.mpr hlt, pre, Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.succ_pos _) hl)⟩
    · rw [mcDivGuess_def]
      simp only [mcDivR1_thm, hlt, if_true, eq, mwDivGuess, holHd, List.tail_cons,
        BitVec.lt_def.mp hlt]
  · obtain ⟨l2, pre, eq, bound⟩ :=
      mcDivTest_thm (BitVec.ofNat width (2 ^ width - 1)) u1 u2 u3 v1 v2 (l - 1) (by omega)
    have hlt' : ¬ u1.toNat < v1.toNat := fun h => hlt (BitVec.lt_def.mpr h)
    refine ⟨l2, ?_, ?_, by omega⟩
    · rw [mcDivGuessPre_def]
      simp only [mcDivR1_thm, hlt, if_false, hnot]
      rw [mcDivR1Pre_def]
      simp only [hlt, if_false]
      exact ⟨fun _ h => h.elim, fun _ => ⟨trivial, pre,
        Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.succ_pos _) hl)⟩⟩
    · rw [mcDivGuess_def]
      simp only [mcDivR1_thm, hlt, if_false, hnot, eq, mwDivGuess, holHd, List.tail_cons,
        hlt']

end Flapjack.Misc.Multiword
