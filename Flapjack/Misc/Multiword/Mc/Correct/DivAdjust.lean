module

public import Flapjack.Misc.Multiword.Mc.Correct.DivTest
public import Flapjack.Misc.Multiword.MulBySingle2

@[expose] public section

/-! Correctness of the machine-code-style quotient digit adjustment and
multiply-subtract steps of HOL's `mc_multiword` division. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Flapjack proof of the local HOL lemma `mc_adj_cmp_thm`. -/
theorem mcAdjCmp_thm {width : Nat} [NeZero width] {r1 h anything : BitVec width}
    {res : Option Bool} :
    mcAdjCmpPre (r1, h, anything) ∧
      mcAdjCmp (r1, h, if res = some true then 1 else 0) =
        (r1, h, if mwCmpAlt [h] [r1] res = some true then 1 else 0) := by
  refine ⟨by rw [mcAdjCmpPre_def]; split_ifs; trivial, ?_⟩
  rw [mcAdjCmp_def]
  simp only [mwCmpAlt, holHd]
  by_cases e : r1 = h
  · subst e; simp
  · by_cases lt : h < r1
    · simp [e, Ne.symm e, lt]
    · simp [e, Ne.symm e, lt]

/-- Flapjack proof of the local HOL lemma `mw_cmp_alt_CONS`. -/
theorem mwCmpAlt_CONS {width : Nat} [NeZero width] (zs ys : List (BitVec width))
    (z q3 : BitVec width) (res : Option Bool) :
    mwCmpAlt zs ys (mwCmpAlt [z] [q3] res) = mwCmpAlt (z :: zs) (q3 :: ys) res := by
  rfl

/-- The result part of `mcAdjCmp_thm`, as a rewrite rule (Flapjack helper). -/
theorem mcAdjCmp_eq {width : Nat} [NeZero width] {r1 h : BitVec width} {res : Option Bool} :
    mcAdjCmp (r1, h, if res = some true then 1 else 0) =
      (r1, h, if mwCmpAlt [h] [r1] res = some true then 1 else 0) :=
  (mcAdjCmp_thm (anything := 0)).2

/-- Flapjack proof of the local HOL lemma `mc_adjust_aux_thm` (before its
specialization). -/
theorem mcAdjustAux_thm_gen {width : Nat} [NeZero width] {r6 r7 : BitVec width} :
    ∀ (ys zs ys1 zs1 zs2 : List (BitVec width)) (res : Option Bool) (r1 r12 : BitVec width)
      (l : Nat),
      zs.length = ys.length + 1 ∧ (ys1 ++ ys).length < 2 ^ width ∧
      (zs1 ++ zs).length < 2 ^ width ∧ ys.length ≤ l →
      ∃ l2,
        mcAdjustAuxPre (l, r1, r6, r7, if res = some true then 1 else 0,
          BitVec.ofNat width (ys1 ++ ys).length, BitVec.ofNat width zs1.length,
          BitVec.ofNat width ys1.length, r12, ys1 ++ ys, zs1 ++ zs ++ zs2) ∧
        mcAdjustAux (l, r1, r6, r7, if res = some true then 1 else 0,
          BitVec.ofNat width (ys1 ++ ys).length, BitVec.ofNat width zs1.length,
          BitVec.ofNat width ys1.length, r12, ys1 ++ ys, zs1 ++ zs ++ zs2) =
          (l2, r6, r7,
            if mwCmpAlt zs (mwMulBySingle2 r6 r7 ys r1 r12) res = some true then 1 else 0,
            BitVec.ofNat width (ys1 ++ ys).length, BitVec.ofNat width (zs1 ++ zs).length,
            BitVec.ofNat width (ys1 ++ ys).length, ys1 ++ ys, zs1 ++ zs ++ zs2) ∧
        l ≤ l2 + ys.length := by
  intro ys
  induction ys with
  | nil =>
    intro zs ys1 zs1 zs2 res r1 r12 l ⟨hz, _, h3, _⟩
    obtain ⟨z, rfl⟩ : ∃ z, zs = [z] := by
      match zs, hz with
      | [z], _ => exact ⟨z, rfl⟩
    simp only [List.append_nil, List.length_append, List.length_singleton] at h3 ⊢
    have tz : (BitVec.ofNat width zs1.length).toNat = zs1.length := ofNat_toNat_of_lt (by omega)
    have ez : holEl zs1.length (zs1 ++ [z] ++ zs2) = z := by
      simpa using holEl_append_length zs1 zs2 z
    refine ⟨l, ?_, ?_, by simp⟩
    · rw [mcAdjustAuxPre_def]; simp [tz]
    · rw [mcAdjustAux_def]
      simp only [if_true, tz, ez, mwMulBySingle2, ofNat_add_one, mcAdjCmp_eq]
      rfl
  | cons y ys ih =>
    intro zs ys1 zs1 zs2 res r1 r12 l ⟨hz, h2, h3, hl⟩
    obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_length_eq_add_one hz
    simp only [List.length_cons, List.length_append] at hz h2 h3 hl ⊢
    obtain ⟨l2, pre, eq, bound⟩ :=
      ih zs (ys1 ++ [y]) (zs1 ++ [z]) zs2
        (mwCmpAlt [z] [(singleMulAdd r7 (singleMulAdd r6 y r1 0).1 r12 0).1] res)
        (singleMulAdd r6 y r1 0).2 (singleMulAdd r7 (singleMulAdd r6 y r1 0).1 r12 0).2 (l - 1)
        ⟨by omega, by simp; omega, by simp; omega, by omega⟩
    have ne : BitVec.ofNat width (ys1.length + (ys.length + 1)) ≠
        BitVec.ofNat width ys1.length := by
      rw [Ne, ofNat_inj h2 (by omega)]; omega
    have tz : (BitVec.ofNat width zs1.length).toNat = zs1.length := ofNat_toNat_of_lt (by omega)
    have ty : (BitVec.ofNat width ys1.length).toNat = ys1.length := ofNat_toNat_of_lt (by omega)
    have ez : holEl zs1.length (zs1 ++ z :: zs ++ zs2) = z := by
      simpa using holEl_append_length zs1 (zs ++ zs2) z
    have ey : holEl ys1.length (ys1 ++ y :: ys) = y := holEl_append_length ys1 ys y
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_cons] at pre eq ez ⊢
    refine ⟨l2, ?_, ?_, by omega⟩
    · rw [mcAdjustAuxPre_def]
      simp only [ne, if_false, tz, ty, ez, ey, mcSingleMul_thm.2, mcAdjCmp_eq, ofNat_add_one]
      refine ⟨by simpa [Nat.add_assoc] using pre, ⟨⟨⟨by simp, mcSingleMul_thm.1⟩,
        mcSingleMul_thm.1⟩, by simp⟩, by omega⟩
    · rw [mcAdjustAux_def]
      simp only [ne, if_false, tz, ty, ez, ey, mcSingleMul_thm.2, mcAdjCmp_eq, ofNat_add_one]
      refine Eq.trans (by simpa [Nat.add_assoc] using eq) ?_
      simp only [mwMulBySingle2, mwCmpAlt_CONS]
      rfl

/-- Flapjack proof of the local HOL lemma `mc_adjust_aux_thm`. -/
theorem mcAdjustAux_thm {width : Nat} [NeZero width] {r6 r7 : BitVec width} :
    ∀ (ys zs zs1 zs2 : List (BitVec width)) (l : Nat),
      zs.length = ys.length + 1 ∧ ys.length < 2 ^ width ∧
      (zs1 ++ zs).length < 2 ^ width ∧ ys.length ≤ l →
      ∃ l2,
        mcAdjustAuxPre (l, 0, r6, r7, 0, BitVec.ofNat width ys.length,
          BitVec.ofNat width zs1.length, 0, 0, ys, zs1 ++ zs ++ zs2) ∧
        mcAdjustAux (l, 0, r6, r7, 0, BitVec.ofNat width ys.length,
          BitVec.ofNat width zs1.length, 0, 0, ys, zs1 ++ zs ++ zs2) =
          (l2, r6, r7,
            if mwCmpAlt zs (mwMulBySingle2 r6 r7 ys 0 0) none = some true then 1 else 0,
            BitVec.ofNat width ys.length, BitVec.ofNat width (zs1 ++ zs).length,
            BitVec.ofNat width ys.length, ys, zs1 ++ zs ++ zs2) ∧
        l ≤ l2 + ys.length := by
  intro ys zs zs1 zs2 l h
  have := mcAdjustAux_thm_gen (r6 := r6) (r7 := r7) ys zs [] zs1 zs2 none 0 0 l
    (by simpa using h)
  simpa using this

/-- Flapjack proof of the local HOL lemma `mc_div_adjust_thm`. -/
theorem mcDivAdjust_thm {width : Nat} [NeZero width] {r6 r7 : BitVec width}
    {ys zs zs1 zs2 : List (BitVec width)} {l : Nat} :
    zs.length = ys.length + 1 ∧ ys.length < 2 ^ width ∧
    (zs1 ++ zs).length < 2 ^ width ∧ ys.length + 1 ≤ l →
    ∃ l2,
      mcDivAdjustPre (l, r6, r7, BitVec.ofNat width ys.length, BitVec.ofNat width zs1.length,
        ys, zs1 ++ zs ++ zs2) ∧
      mcDivAdjust (l, r6, r7, BitVec.ofNat width ys.length, BitVec.ofNat width zs1.length,
        ys, zs1 ++ zs ++ zs2) =
        (l2, r6, mwDivAdjust r7 zs (mwMulBySingle r6 ys).dropLast,
          BitVec.ofNat width ys.length, BitVec.ofNat width (zs1 ++ zs).length,
          BitVec.ofNat width ys.length, ys, zs1 ++ zs ++ zs2) ∧
      l ≤ l2 + ys.length + 1 := by
  rintro ⟨hz, hy, h3, hl⟩
  obtain ⟨l2, pre, eq, bound⟩ :=
    mcAdjustAux_thm (r6 := r6) (r7 := r7) ys zs zs1 zs2 (l - 1) ⟨hz, hy, h3, by omega⟩
  have alt : mwCmpAlt zs (mwMulBySingle2 r6 r7 ys 0 0) none =
      mwCmp zs (mwMulBySingle2 r6 r7 ys 0 0) := by
    rw [mwCmp_alt_thm]
    rw [mwMulBySingle2_thm, length_mwMulBySingle, List.length_dropLast, length_mwMulBySingle]
    omega
  rw [alt, mwMulBySingle2_thm] at eq
  have z0 : (BitVec.ofNat width 0 : BitVec width) = 0 := rfl
  refine ⟨l2, ?_, ?_, by omega⟩
  · rw [mcDivAdjustPre_def]
    simp only [eq]
    split_ifs <;> exact ⟨pre, by omega⟩
  · rw [mcDivAdjust_def]
    simp only [eq, mwDivAdjust]
    by_cases hc : mwCmp zs (mwMulBySingle r7 (mwMulBySingle r6 ys).dropLast) = some true
    · have ne1 : (1 : BitVec width) ≠ 0 := by simp [NeZero.ne]
      simp only [hc, if_true, ne1, if_false]
      by_cases h0 : r7 = 0
      · subst h0; simp
      · simp only [h0, if_false, (mcSub1_thm r7).2.symm, mcSub1_def]
    · simp only [hc, if_false]
      split_ifs <;> rfl

/-- Flapjack proof of the local HOL lemma `mc_div_sub_thm`. -/
theorem mcDivSub_thm {width : Nat} [NeZero width] {r0 r3 : BitVec width} {c : Bool} :
    mcDivSubPre (r0, r3, b2w c) ∧
      mcDivSub (r0, r3, b2w c) = (r0, (singleSub r3 r0 c).1, b2w (singleSub r3 r0 c).2) := by
  refine ⟨?_, ?_⟩
  · rw [mcDivSubPre_def]; exact b2w_zero_or_one c
  · rw [mcDivSub_def]; simp only [singleSubWord_b2w]

/-- Flapjack proof of the local HOL lemma `mc_div_sub_loop_thm` (before its
specialization). -/
theorem mcDivSubLoop_thm_gen {width : Nat} [NeZero width] {r6 r7 : BitVec width} :
    ∀ (ys zs ys1 zs1 zs2 : List (BitVec width)) (c : Bool) (r1 r12 : BitVec width) (l : Nat),
      zs.length = ys.length + 1 ∧ (ys1 ++ ys).length < 2 ^ width ∧
      (zs1 ++ zs).length < 2 ^ width ∧ ys.length ≤ l →
      ∃ l2,
        mcDivSubLoopPre (l, r1, r6, r7, b2w c,
          BitVec.ofNat width (ys1 ++ ys).length, BitVec.ofNat width zs1.length,
          BitVec.ofNat width ys1.length, r12, ys1 ++ ys, zs1 ++ zs ++ zs2) ∧
        mcDivSubLoop (l, r1, r6, r7, b2w c,
          BitVec.ofNat width (ys1 ++ ys).length, BitVec.ofNat width zs1.length,
          BitVec.ofNat width ys1.length, r12, ys1 ++ ys, zs1 ++ zs ++ zs2) =
          (l2, r6, r7, BitVec.ofNat width (ys1 ++ ys).length,
            BitVec.ofNat width (zs1 ++ zs).length, BitVec.ofNat width (ys1 ++ ys).length,
            ys1 ++ ys, zs1 ++ (mwSub zs (mwMulBySingle2 r6 r7 ys r1 r12) c).1 ++ zs2) ∧
        l ≤ l2 + ys.length := by
  intro ys
  induction ys with
  | nil =>
    intro zs ys1 zs1 zs2 c r1 r12 l ⟨hz, _, h3, _⟩
    obtain ⟨z, rfl⟩ : ∃ z, zs = [z] := by
      match zs, hz with
      | [z], _ => exact ⟨z, rfl⟩
    simp only [List.append_nil, List.length_append, List.length_singleton] at h3 ⊢
    have tz : (BitVec.ofNat width zs1.length).toNat = zs1.length := ofNat_toNat_of_lt (by omega)
    have ez : holEl zs1.length (zs1 ++ [z] ++ zs2) = z := by
      simpa using holEl_append_length zs1 zs2 z
    have sz : ∀ v, (zs1 ++ [z] ++ zs2).set zs1.length v = zs1 ++ [v] ++ zs2 := by
      intro v; simp
    refine ⟨l, ?_, ?_, by simp⟩
    · rw [mcDivSubLoopPre_def]
      simp only [if_true, tz, ez, mcDivSub_thm.2]
      exact ⟨by simp, mcDivSub_thm.1⟩
    · rw [mcDivSubLoop_def]
      simp only [if_true, tz, ez, mcDivSub_thm.2, sz, ofNat_add_one, mwMulBySingle2, mwSub]
  | cons y ys ih =>
    intro zs ys1 zs1 zs2 c r1 r12 l ⟨hz, h2, h3, hl⟩
    obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_length_eq_add_one hz
    simp only [List.length_cons, List.length_append] at hz h2 h3 hl ⊢
    obtain ⟨l2, pre, eq, bound⟩ :=
      ih zs (ys1 ++ [y])
        (zs1 ++ [(singleSub z (singleMulAdd r7 (singleMulAdd r6 y r1 0).1 r12 0).1 c).1]) zs2
        (singleSub z (singleMulAdd r7 (singleMulAdd r6 y r1 0).1 r12 0).1 c).2
        (singleMulAdd r6 y r1 0).2 (singleMulAdd r7 (singleMulAdd r6 y r1 0).1 r12 0).2 (l - 1)
        ⟨by omega, by simp; omega, by simp; omega, by omega⟩
    have ne : BitVec.ofNat width (ys1.length + (ys.length + 1)) ≠
        BitVec.ofNat width ys1.length := by
      rw [Ne, ofNat_inj h2 (by omega)]; omega
    have tz : (BitVec.ofNat width zs1.length).toNat = zs1.length := ofNat_toNat_of_lt (by omega)
    have ty : (BitVec.ofNat width ys1.length).toNat = ys1.length := ofNat_toNat_of_lt (by omega)
    have ez : holEl zs1.length (zs1 ++ z :: zs ++ zs2) = z := by
      simpa using holEl_append_length zs1 (zs ++ zs2) z
    have ey : holEl ys1.length (ys1 ++ y :: ys) = y := holEl_append_length ys1 ys y
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_cons] at pre eq ez ⊢
    refine ⟨l2, ?_, ?_, by omega⟩
    · rw [mcDivSubLoopPre_def]
      simp only [ne, if_false, tz, ty, ez, ey, mcSingleMul_thm.2, mcDivSub_thm.2,
        ofNat_add_one]
      refine ⟨by simpa [Nat.add_assoc] using pre, ⟨⟨⟨⟨by simp, mcSingleMul_thm.1⟩,
        mcSingleMul_thm.1⟩, by simp⟩, mcDivSub_thm.1⟩, by omega⟩
    · rw [mcDivSubLoop_def]
      simp only [ne, if_false, tz, ty, ez, ey, mcSingleMul_thm.2, mcDivSub_thm.2,
        ofNat_add_one]
      refine Eq.trans (by simpa [Nat.add_assoc] using eq) ?_
      simp only [mwMulBySingle2, mwSub, List.cons_append]
      rfl

/-- Flapjack proof of the local HOL lemma `mc_div_sub_loop_thm`. -/
theorem mcDivSubLoop_thm {width : Nat} [NeZero width] {r6 r7 : BitVec width} :
    ∀ (ys zs zs1 zs2 : List (BitVec width)) (l : Nat),
      zs.length = ys.length + 1 ∧ ys.length < 2 ^ width ∧
      (zs1 ++ zs).length < 2 ^ width ∧ ys.length ≤ l →
      ∃ l2,
        mcDivSubLoopPre (l, 0, r6, r7, 1, BitVec.ofNat width ys.length,
          BitVec.ofNat width zs1.length, 0, 0, ys, zs1 ++ zs ++ zs2) ∧
        mcDivSubLoop (l, 0, r6, r7, 1, BitVec.ofNat width ys.length,
          BitVec.ofNat width zs1.length, 0, 0, ys, zs1 ++ zs ++ zs2) =
          (l2, r6, r7, BitVec.ofNat width ys.length,
            BitVec.ofNat width (zs1 ++ zs).length, BitVec.ofNat width ys.length,
            ys, zs1 ++ (mwSub zs (mwMulBySingle2 r6 r7 ys 0 0) true).1 ++ zs2) ∧
        l ≤ l2 + ys.length := by
  intro ys zs zs1 zs2 l h
  have bT : (b2w true : BitVec width) = 1 := by simp [b2w, b2n]
  have := mcDivSubLoop_thm_gen (r6 := r6) (r7 := r7) ys zs [] zs1 zs2 true 0 0 l
    (by simpa using h)
  simpa [bT] using this

end Flapjack.Misc.Multiword
