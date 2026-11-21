module

public import Flapjack.Misc.Multiword.Mc.Correct.Add
public import Flapjack.Misc.Multiword.DivTest

@[expose] public section

/-! Correctness of the machine-code-style unsigned subtraction of HOL's
`mc_multiword`. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Flapjack proof of the local HOL lemma `mc_sub_loop1_thm`. -/
theorem mcSubLoop1_thm {width : Nat} [NeZero width] :
    ∀ (xs ys zs xs1 ys1 zs1 xs2 ys2 zs2 : List (BitVec width)) (r8 r9 : BitVec width)
      (c : Bool) (l : Nat),
      ys1.length = xs1.length ∧ zs1.length = xs1.length ∧ ys.length = xs.length ∧
      zs.length = xs.length ∧ (xs1 ++ xs).length + 1 < 2 ^ width ∧ xs.length ≤ l →
      ∃ r8' r9' l2,
        mcSubLoop1Pre (l, BitVec.ofNat width (xs.length + 1), b2w c, r8, r9,
          BitVec.ofNat width xs1.length, xs1 ++ xs ++ xs2, ys1 ++ ys ++ ys2, zs1 ++ zs ++ zs2) ∧
        mcSubLoop1 (l, BitVec.ofNat width (xs.length + 1), b2w c, r8, r9,
          BitVec.ofNat width xs1.length, xs1 ++ xs ++ xs2, ys1 ++ ys ++ ys2, zs1 ++ zs ++ zs2) =
          (l2, 0, b2w (mwSub xs ys c).2, r8', r9', BitVec.ofNat width (xs1 ++ xs).length,
            xs1 ++ xs ++ xs2, ys1 ++ ys ++ ys2, zs1 ++ (mwSub xs ys c).1 ++ zs2) ∧
        l ≤ l2 + xs.length := by
  intro xs
  induction xs with
  | nil =>
    intro ys zs xs1 ys1 zs1 xs2 ys2 zs2 r8 r9 c l ⟨_, _, h3, h4, _, _⟩
    rw [List.eq_nil_of_length_eq_zero h3, List.eq_nil_of_length_eq_zero h4]
    refine ⟨r8, r9, l, ?_, ?_, by simp⟩
    · rw [mcSubLoop1Pre_def]; simp
    · rw [mcSubLoop1_def]; simp [mwSub]
  | cons x xs ih =>
    intro ys zs xs1 ys1 zs1 xs2 ys2 zs2 r8 r9 c l ⟨h1, h2, h3, h4, h5, h6⟩
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one h3
    obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_length_eq_add_one h4
    simp only [List.length_cons, List.length_append] at h3 h4 h5 h6 ⊢
    obtain ⟨r8', r9', l2, pre, eq, bound⟩ :=
      ih ys zs (xs1 ++ [x]) (ys1 ++ [y]) (zs1 ++ [(singleSub x y c).1]) xs2 ys2 zs2
        (singleSub x y c).1 y (singleSub x y c).2 (l - 1)
        ⟨by simp; omega, by simp; omega, by omega, by omega, by simp; omega, by omega⟩
    have ne : BitVec.ofNat width (xs.length + 1 + 1) ≠ 1 := by
      rw [Ne, ofNat_succ_eq_one (by omega)]; omega
    have sub := ofNat_succ_sub_one (width := width) (n := xs.length + 1) (by omega)
    have tn : (BitVec.ofNat width xs1.length).toNat = xs1.length := ofNat_toNat_of_lt (by omega)
    have ex : holEl xs1.length (xs1 ++ x :: xs ++ xs2) = x := by
      simpa using holEl_append_length xs1 (xs ++ xs2) x
    have ey : holEl xs1.length (ys1 ++ y :: ys ++ ys2) = y := by
      rw [← h1]; simpa using holEl_append_length ys1 (ys ++ ys2) y
    have sz : (zs1 ++ z :: zs ++ zs2).set xs1.length (singleSub x y c).1 =
        zs1 ++ [(singleSub x y c).1] ++ zs ++ zs2 := by
      rw [← h2]; simp
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append, List.length_singleton] at pre eq sz ex ey ⊢
    refine ⟨r8', r9', l2, ?_, ?_, by omega⟩
    · rw [mcSubLoop1Pre_def]
      simp only [ne, if_false, sub, tn, ex, ey, singleSubWord_b2w, sz, ofNat_add_one]
      refine ⟨pre, ⟨⟨⟨by simp, by simp; omega⟩, b2w_zero_or_one c⟩, by simp; omega⟩, by omega⟩
    · rw [mcSubLoop1_def]
      simp only [ne, if_false, sub, tn, ex, ey, singleSubWord_b2w, sz, ofNat_add_one, eq]
      simp only [mwSub, List.cons_append, List.length_cons]

/-- Flapjack proof of the local HOL lemma `mc_sub_loop2_thm`. -/
theorem mcSubLoop2_thm {width : Nat} [NeZero width] :
    ∀ (xs zs xs1 zs1 xs2 zs2 : List (BitVec width)) (r8 : BitVec width) (c : Bool) (l : Nat),
      zs1.length = xs1.length ∧ zs.length = xs.length ∧
      (xs1 ++ xs).length + 1 < 2 ^ width ∧ xs.length ≤ l →
      ∃ r8' r9' l2,
        mcSubLoop2Pre (l, BitVec.ofNat width (xs.length + 1), b2w c, r8, 0,
          BitVec.ofNat width xs1.length, xs1 ++ xs ++ xs2, zs1 ++ zs ++ zs2) ∧
        mcSubLoop2 (l, BitVec.ofNat width (xs.length + 1), b2w c, r8, 0,
          BitVec.ofNat width xs1.length, xs1 ++ xs ++ xs2, zs1 ++ zs ++ zs2) =
          (l2, 0, b2w (mwSub xs [] c).2, r8', r9',
            BitVec.ofNat width (xs1 ++ xs).length, xs1 ++ xs ++ xs2,
            zs1 ++ (mwSub xs [] c).1 ++ zs2) ∧
        l ≤ l2 + xs.length := by
  intro xs
  induction xs with
  | nil =>
    intro zs xs1 zs1 xs2 zs2 r8 c l ⟨_, h4, _, _⟩
    rw [List.eq_nil_of_length_eq_zero h4]
    refine ⟨r8, 0, l, ?_, ?_, by simp⟩
    · rw [mcSubLoop2Pre_def]; simp
    · rw [mcSubLoop2_def]; simp [mwSub]
  | cons x xs ih =>
    intro zs xs1 zs1 xs2 zs2 r8 c l ⟨h2, h4, h5, h6⟩
    obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_length_eq_add_one h4
    simp only [List.length_cons, List.length_append] at h4 h5 h6 ⊢
    obtain ⟨r8', r9', l2, pre, eq, bound⟩ :=
      ih zs (xs1 ++ [x]) (zs1 ++ [(singleSub x 0 c).1]) xs2 zs2
        (singleSub x 0 c).1 (singleSub x 0 c).2 (l - 1)
        ⟨by simp; omega, by omega, by simp; omega, by omega⟩
    have ne : BitVec.ofNat width (xs.length + 1 + 1) ≠ 1 := by
      rw [Ne, ofNat_succ_eq_one (by omega)]; omega
    have sub := ofNat_succ_sub_one (width := width) (n := xs.length + 1) (by omega)
    have tn : (BitVec.ofNat width xs1.length).toNat = xs1.length := ofNat_toNat_of_lt (by omega)
    have ex : holEl xs1.length (xs1 ++ x :: xs ++ xs2) = x := by
      simpa using holEl_append_length xs1 (xs ++ xs2) x
    have sz : (zs1 ++ z :: zs ++ zs2).set xs1.length (singleSub x 0 c).1 =
        zs1 ++ [(singleSub x 0 c).1] ++ zs ++ zs2 := by
      rw [← h2]; simp
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_singleton] at pre eq sz ex ⊢
    refine ⟨r8', r9', l2, ?_, ?_, by omega⟩
    · rw [mcSubLoop2Pre_def]
      simp only [ne, if_false, sub, tn, ex, singleSubWord_b2w, sz, ofNat_add_one]
      refine ⟨pre, ⟨⟨by simp, b2w_zero_or_one c⟩, by simp; omega⟩, by omega⟩
    · rw [mcSubLoop2_def]
      simp only [ne, if_false, sub, tn, ex, singleSubWord_b2w, sz, ofNat_add_one, eq]
      simp only [mwSub, List.cons_append, List.length_cons]

/-- Flapjack proof of the local HOL lemma `mc_fix_thm`. -/
theorem mcFix_thm {width : Nat} [NeZero width] :
    ∀ (zs zs1 : List (BitVec width)) (r8 : BitVec width) (l : Nat),
      zs.length < 2 ^ width ∧ zs.length ≤ l →
      ∃ r8' l2,
        mcFixPre (l, r8, BitVec.ofNat width zs.length, zs ++ zs1) ∧
        mcFix (l, r8, BitVec.ofNat width zs.length, zs ++ zs1) =
          (l2, r8', BitVec.ofNat width (mwFix zs).length,
            mwFix zs ++ List.replicate (zs.length - (mwFix zs).length) 0 ++ zs1) ∧
        l ≤ l2 + zs.length := by
  intro zs
  induction zs using snoc_induction with
  | nil =>
    intro zs1 r8 l _
    refine ⟨r8, l, ?_, ?_, by simp⟩
    · rw [mcFixPre_def]; simp
    · rw [mcFix_def, mwFix]; simp
  | snoc zs x ih =>
    intro zs1 r8 l ⟨hlt, hle⟩
    simp only [List.length_append, List.length_singleton] at hlt hle ⊢
    have ne : BitVec.ofNat width (zs.length + 1) ≠ 0 := by
      rw [Ne, ofNat_eq_zero hlt]; omega
    have sub := ofNat_succ_sub_one (width := width) (n := zs.length) hlt
    have tn : (BitVec.ofNat width zs.length).toNat = zs.length := ofNat_toNat_of_lt (by omega)
    have ex : holEl zs.length (zs ++ [x] ++ zs1) = x := by
      simpa using holEl_append_length zs zs1 x
    have lf := length_mwFix zs
    rw [mcFixPre_def, mcFix_def, mwFix_snoc]
    simp only [ne, if_false, sub, tn, ex]
    by_cases hx : x = 0
    · subst hx
      obtain ⟨r8', l2, pre, eq, bound⟩ := ih (0 :: zs1) 0 (l - 1) ⟨by omega, by omega⟩
      simp only [if_true, List.append_assoc, List.singleton_append] at pre eq ⊢
      refine ⟨r8', l2, ⟨pre, by simp, by omega⟩, ?_, by omega⟩
      rw [eq, show zs.length + 1 - (mwFix zs).length = zs.length - (mwFix zs).length + 1 by omega,
        replicate_SNOC]
      simp
    · simp only [hx, if_false]
      refine ⟨x, l, by simp, ?_, by omega⟩
      rw [ofNat_add_one]; simp

/-- Flapjack proof of the local HOL lemma `mc_sub_thm`. -/
theorem mcSub_thm {width : Nat} [NeZero width] :
    ∀ (xs ys zs zs2 : List (BitVec width)) (l : Nat),
      ys.length ≤ xs.length ∧ zs.length = xs.length ∧
      xs.length + 1 < 2 ^ width ∧ xs.length + xs.length + 3 ≤ l →
      ∃ (r1' r2' r8' r9' _r10' : BitVec width) (l2 : Nat),
        mcSubPre (l, BitVec.ofNat width ys.length, BitVec.ofNat width xs.length, 0, 0, 0,
          xs, ys, zs ++ zs2) ∧
        mcSub (l, BitVec.ofNat width ys.length, BitVec.ofNat width xs.length, 0, 0, 0,
          xs, ys, zs ++ zs2) =
          (l2, r1', r2', r8', r9', BitVec.ofNat width (mwSubv xs ys).length, xs, ys,
            mwSubv xs ys ++ List.replicate (xs.length - (mwSubv xs ys).length) 0 ++ zs2) ∧
        l ≤ l2 + xs.length + xs.length + 3 := by
  rintro xs ys zs zs2 l ⟨hyx, hz, hx, hl⟩
  obtain ⟨xs1, xs2, rfl, h1⟩ := less_eq_length xs ys.length hyx
  simp only [List.length_append] at hx hl hz
  have hsub := mwSub_APPEND xs1 xs2 ys true h1
  rcases e1 : mwSub xs1 ys true with ⟨qs1, c1⟩
  rcases e2 : mwSub xs2 [] c1 with ⟨qs2, c2⟩
  simp only [e1, e2] at hsub
  have lq1 := length_mwSub _ _ _ _ _ e1
  have lq2 := length_mwSub _ _ _ _ _ e2
  obtain ⟨zs1, zs3, rfl, hz1⟩ := less_eq_length zs xs1.length (by omega)
  simp only [List.length_append] at hz
  have hz3 : zs3.length = xs2.length := by omega
  have bT : (1 : BitVec width) = b2w true := by simp [b2w, b2n]
  obtain ⟨r8a, r9a, la, pre1, eq1, bound1⟩ :=
    mcSubLoop1_thm xs1 ys zs1 [] [] [] xs2 [] (zs3 ++ zs2) 0 0 true (l - 1)
      ⟨rfl, rfl, h1.symm, by omega, by simp; omega, by omega⟩
  simp only [List.nil_append, List.append_nil, List.length_nil, e1] at pre1 eq1
  obtain ⟨r8b, r9b, lb, pre2, eq2, bound2⟩ :=
    mcSubLoop2_thm xs2 zs3 xs1 qs1 [] zs2 r8a c1 (la - 1)
      ⟨by omega, hz3, by simp; omega, by omega⟩
  simp only [List.append_nil, e2, List.length_append] at pre2 eq2
  have lfix : (qs1 ++ qs2).length < 2 ^ width := by simp; omega
  obtain ⟨r8c, lc, pre3, eq3, bound3⟩ := mcFix_thm (qs1 ++ qs2) zs2 r8b (lb - 1)
    ⟨lfix, by simp only [List.length_append]; omega⟩
  have sub : BitVec.ofNat width (xs1.length + xs2.length) - BitVec.ofNat width ys.length =
      BitVec.ofNat width xs2.length := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ofNat_toNat_of_lt (by omega),
      ofNat_toNat_of_lt (by omega)]; omega), ofNat_toNat_of_lt (by omega),
      ofNat_toNat_of_lt (by omega), ofNat_toNat_of_lt (by omega)]
    omega
  have z0 : (BitVec.ofNat width 0 : BitVec width) = 0 := rfl
  have s0 : (0 : BitVec width) - 0 = 0 := BitVec.eq_of_toNat_eq (by simp)
  rw [← bT, z0] at pre1 eq1
  simp only [List.append_assoc] at pre1 eq1 pre2 eq2
  simp only [List.append_assoc, List.length_append] at pre3 eq3
  rw [h1] at pre1 eq1 pre2 eq2
  have len3 : BitVec.ofNat width (ys.length + xs2.length) =
      BitVec.ofNat width (qs1.length + qs2.length) := by
    congr 1; omega
  rw [len3] at eq2
  have hv : mwSubv (xs1 ++ xs2) ys = mwFix (qs1 ++ qs2) := by rw [mwSubv, hsub]
  simp only [mcSubPre_def, mcSub_def, mcSubLoopPre_def, mcSubLoop_def, List.length_append, sub,
    ofNat_add_one, List.append_assoc, s0, eq1, eq2, eq3, hv]
  simp only [List.length_append] at bound3
  refine ⟨0, BitVec.ofNat width (xs2.length + 1), r8c, r9b, 0, lc,
    ⟨⟨⟨pre1, by omega⟩, pre2, by omega⟩, pre3, by omega⟩, ?_, by omega⟩
  rw [show qs1.length + qs2.length = xs1.length + xs2.length by omega]

end Flapjack.Misc.Multiword
