module

public import Flapjack.Misc.Multiword.Mc.Correct.Compare
public import Flapjack.Misc.Multiword.DivAux

@[expose] public section

/-! Correctness of the machine-code-style unsigned addition of HOL's
`mc_multiword`. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Flapjack proof of the local HOL lemma `mc_add_loop1_thm`. -/
theorem mcAddLoop1_thm {width : Nat} [NeZero width] :
    ∀ (xs ys zs xs1 ys1 zs1 xs2 ys2 zs2 : List (BitVec width)) (r8 r9 : BitVec width)
      (c : Bool) (l : Nat),
      ys1.length = xs1.length ∧ zs1.length = xs1.length ∧ ys.length = xs.length ∧
      zs.length = xs.length ∧ (xs1 ++ xs).length + 1 < 2 ^ width ∧ xs.length ≤ l →
      ∃ r8' r9' l2,
        mcAddLoop1Pre (l, BitVec.ofNat width (xs.length + 1), b2w c, r8, r9,
          BitVec.ofNat width xs1.length, xs1 ++ xs ++ xs2, ys1 ++ ys ++ ys2, zs1 ++ zs ++ zs2) ∧
        mcAddLoop1 (l, BitVec.ofNat width (xs.length + 1), b2w c, r8, r9,
          BitVec.ofNat width xs1.length, xs1 ++ xs ++ xs2, ys1 ++ ys ++ ys2, zs1 ++ zs ++ zs2) =
          (l2, 0, b2w (mwAdd xs ys c).2, r8', r9', BitVec.ofNat width (xs1 ++ xs).length,
            xs1 ++ xs ++ xs2, ys1 ++ ys ++ ys2, zs1 ++ (mwAdd xs ys c).1 ++ zs2) ∧
        l ≤ l2 + xs.length := by
  intro xs
  induction xs with
  | nil =>
    intro ys zs xs1 ys1 zs1 xs2 ys2 zs2 r8 r9 c l ⟨_, _, h3, h4, _, _⟩
    rw [List.eq_nil_of_length_eq_zero h3, List.eq_nil_of_length_eq_zero h4]
    refine ⟨r8, r9, l, ?_, ?_, by simp⟩
    · rw [mcAddLoop1Pre_def]; simp
    · rw [mcAddLoop1_def]; simp [mwAdd]
  | cons x xs ih =>
    intro ys zs xs1 ys1 zs1 xs2 ys2 zs2 r8 r9 c l ⟨h1, h2, h3, h4, h5, h6⟩
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one h3
    obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_length_eq_add_one h4
    simp only [List.length_cons, List.length_append] at h3 h4 h5 h6 ⊢
    obtain ⟨r8', r9', l2, pre, eq, bound⟩ :=
      ih ys zs (xs1 ++ [x]) (ys1 ++ [y]) (zs1 ++ [(singleAdd x y c).1]) xs2 ys2 zs2
        (singleAdd x y c).1 y (singleAdd x y c).2 (l - 1)
        ⟨by simp; omega, by simp; omega, by omega, by omega, by simp; omega, by omega⟩
    have ne : BitVec.ofNat width (xs.length + 1 + 1) ≠ 1 := by
      rw [Ne, ofNat_succ_eq_one (by omega)]; omega
    have sub := ofNat_succ_sub_one (width := width) (n := xs.length + 1) (by omega)
    have tn : (BitVec.ofNat width xs1.length).toNat = xs1.length := ofNat_toNat_of_lt (by omega)
    have ex : holEl xs1.length (xs1 ++ x :: xs ++ xs2) = x := by
      simpa using holEl_append_length xs1 (xs ++ xs2) x
    have ey : holEl xs1.length (ys1 ++ y :: ys ++ ys2) = y := by
      rw [← h1]; simpa using holEl_append_length ys1 (ys ++ ys2) y
    have sz : (zs1 ++ z :: zs ++ zs2).set xs1.length (singleAdd x y c).1 =
        zs1 ++ [(singleAdd x y c).1] ++ zs ++ zs2 := by
      rw [← h2]; simp
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append, List.length_singleton] at pre eq sz ex ey ⊢
    refine ⟨r8', r9', l2, ?_, ?_, by omega⟩
    · rw [mcAddLoop1Pre_def]
      simp only [ne, if_false, sub, tn, ex, ey, singleAddWord_b2w, sz, ofNat_add_one]
      refine ⟨pre, ⟨⟨⟨by simp, by simp; omega⟩, b2w_zero_or_one c⟩, by simp; omega⟩, by omega⟩
    · rw [mcAddLoop1_def]
      simp only [ne, if_false, sub, tn, ex, ey, singleAddWord_b2w, sz, ofNat_add_one, eq]
      simp only [mwAdd, holHd, List.tail_cons, List.cons_append, List.length_cons]

/-- Flapjack proof of the local HOL lemma `mc_add_loop2_thm`. -/
theorem mcAddLoop2_thm {width : Nat} [NeZero width] :
    ∀ (xs zs xs1 zs1 xs2 zs2 : List (BitVec width)) (r8 : BitVec width) (c : Bool) (l : Nat),
      zs1.length = xs1.length ∧ zs.length = xs.length ∧
      (xs1 ++ xs).length + 1 < 2 ^ width ∧ xs.length ≤ l →
      ∃ r8' r9' l2,
        mcAddLoop2Pre (l, BitVec.ofNat width (xs.length + 1), b2w c, r8, 0,
          BitVec.ofNat width xs1.length, xs1 ++ xs ++ xs2, zs1 ++ zs ++ zs2) ∧
        mcAddLoop2 (l, BitVec.ofNat width (xs.length + 1), b2w c, r8, 0,
          BitVec.ofNat width xs1.length, xs1 ++ xs ++ xs2, zs1 ++ zs ++ zs2) =
          (l2, 0, b2w (mwAdd xs (xs.map fun _ => 0) c).2, r8', r9',
            BitVec.ofNat width (xs1 ++ xs).length, xs1 ++ xs ++ xs2,
            zs1 ++ (mwAdd xs (xs.map fun _ => 0) c).1 ++ zs2) ∧
        l ≤ l2 + xs.length := by
  intro xs
  induction xs with
  | nil =>
    intro zs xs1 zs1 xs2 zs2 r8 c l ⟨_, h4, _, _⟩
    rw [List.eq_nil_of_length_eq_zero h4]
    refine ⟨r8, 0, l, ?_, ?_, by simp⟩
    · rw [mcAddLoop2Pre_def]; simp
    · rw [mcAddLoop2_def]; simp [mwAdd]
  | cons x xs ih =>
    intro zs xs1 zs1 xs2 zs2 r8 c l ⟨h2, h4, h5, h6⟩
    obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_length_eq_add_one h4
    simp only [List.length_cons, List.length_append] at h4 h5 h6 ⊢
    obtain ⟨r8', r9', l2, pre, eq, bound⟩ :=
      ih zs (xs1 ++ [x]) (zs1 ++ [(singleAdd x 0 c).1]) xs2 zs2
        (singleAdd x 0 c).1 (singleAdd x 0 c).2 (l - 1)
        ⟨by simp; omega, by omega, by simp; omega, by omega⟩
    have ne : BitVec.ofNat width (xs.length + 1 + 1) ≠ 1 := by
      rw [Ne, ofNat_succ_eq_one (by omega)]; omega
    have sub := ofNat_succ_sub_one (width := width) (n := xs.length + 1) (by omega)
    have tn : (BitVec.ofNat width xs1.length).toNat = xs1.length := ofNat_toNat_of_lt (by omega)
    have ex : holEl xs1.length (xs1 ++ x :: xs ++ xs2) = x := by
      simpa using holEl_append_length xs1 (xs ++ xs2) x
    have sz : (zs1 ++ z :: zs ++ zs2).set xs1.length (singleAdd x 0 c).1 =
        zs1 ++ [(singleAdd x 0 c).1] ++ zs ++ zs2 := by
      rw [← h2]; simp
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_singleton] at pre eq sz ex ⊢
    refine ⟨r8', r9', l2, ?_, ?_, by omega⟩
    · rw [mcAddLoop2Pre_def]
      simp only [ne, if_false, sub, tn, ex, singleAddWord_b2w, sz, ofNat_add_one]
      refine ⟨pre, ⟨⟨by simp, b2w_zero_or_one c⟩, by simp; omega⟩, by omega⟩
    · rw [mcAddLoop2_def]
      simp only [ne, if_false, sub, tn, ex, singleAddWord_b2w, sz, ofNat_add_one, eq]
      simp only [mwAdd, holHd, List.map_cons, List.tail_cons, List.cons_append, List.length_cons]

/-- Flapjack proof of the local HOL lemma `mc_add_thm`. -/
theorem mcAdd_thm {width : Nat} [NeZero width] :
    ∀ (xs ys zs zs2 : List (BitVec width)) (l : Nat),
      ys.length ≤ xs.length ∧ zs.length = (mwAddv xs ys false).length ∧
      xs.length + 1 < 2 ^ width ∧ xs.length + 2 ≤ l →
      ∃ (r1' r2' r8' r9' _r10' : BitVec width) (l2 : Nat),
        mcAddPre (l, BitVec.ofNat width ys.length, BitVec.ofNat width xs.length, 0, 0, 0,
          xs, ys, zs ++ zs2) ∧
        mcAdd (l, BitVec.ofNat width ys.length, BitVec.ofNat width xs.length, 0, 0, 0,
          xs, ys, zs ++ zs2) =
          (l2, r1', r2', r8', r9', BitVec.ofNat width (mwAddv xs ys false).length, xs, ys,
            mwAddv xs ys false ++ zs2) ∧
        l ≤ l2 + xs.length + 2 := by
  rintro xs ys zs zs2 l ⟨hyx, hz, hx, hl⟩
  obtain ⟨xs1, xs2, rfl, h1⟩ := less_eq_length xs ys.length hyx
  simp only [List.length_append] at hx hl
  have hadd := mwAddv_EQ_mwAdd xs1 xs2 ys false h1.symm
  rcases e1 : mwAdd xs1 ys false with ⟨qs1, c1⟩
  rcases e2 : mwAdd xs2 (xs2.map fun _ => 0) c1 with ⟨qs2, c2⟩
  simp only [e1, e2] at hadd
  have lq1 := length_mwAdd _ _ _ _ _ e1
  have lq2 := length_mwAdd _ _ _ _ _ e2
  rw [hadd] at hz ⊢
  simp only [List.length_append] at hz
  obtain ⟨zs1, zs', rfl, hz1⟩ := less_eq_length zs xs1.length (by omega)
  obtain ⟨zs3, zs4, rfl, hz3⟩ := less_eq_length zs' xs2.length (by simp at hz; omega)
  simp only [List.length_append] at hz
  have hz4 : zs4.length = (if c2 then [(1 : BitVec width)] else []).length := by omega

  have bF : (0 : BitVec width) = b2w false := by simp [b2w, b2n]
  obtain ⟨r8a, r9a, la, pre1, eq1, bound1⟩ :=
    mcAddLoop1_thm xs1 ys zs1 [] [] [] (xs2) [] (zs3 ++ zs4 ++ zs2) 0 0 false (l - 1)
      ⟨rfl, rfl, h1.symm, by omega, by simp; omega, by omega⟩
  simp only [List.nil_append, List.append_nil, List.length_nil, e1] at pre1 eq1
  obtain ⟨r8b, r9b, lb, pre2, eq2, bound2⟩ :=
    mcAddLoop2_thm xs2 zs3 xs1 qs1 [] (zs4 ++ zs2) r8a c1 (la - 1)
      ⟨by omega, hz3, by simp; omega, by omega⟩
  simp only [List.append_nil, e2, List.length_append] at pre2 eq2
  have sub : BitVec.ofNat width (xs1.length + xs2.length) - BitVec.ofNat width ys.length =
      BitVec.ofNat width xs2.length := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ofNat_toNat_of_lt (by omega),
      ofNat_toNat_of_lt (by omega)]; omega), ofNat_toNat_of_lt (by omega),
      ofNat_toNat_of_lt (by omega), ofNat_toNat_of_lt (by omega)]
    omega
  have z0 : (BitVec.ofNat width 0 : BitVec width) = 0 := rfl
  rw [← bF, z0] at pre1 eq1
  simp only [List.append_assoc] at pre1 eq1 pre2 eq2
  rw [h1] at pre1 eq1 pre2 eq2
  simp only [mcAddPre_def, mcAdd_def, mcAddLoopPre_def, mcAddLoop_def, List.length_append, sub,
    ofNat_add_one, List.append_assoc, eq1, eq2]
  have lb2 : ys.length + xs2.length < 2 ^ width := by omega
  cases c2
  · have hb : (b2w false : BitVec width) = 0 := by simp [b2w, b2n]
    have : zs4 = [] := List.eq_nil_of_length_eq_zero (by simpa using hz4)
    subst this
    simp only [hb, if_true, Bool.false_eq_true, if_false, List.nil_append]
    refine ⟨0, BitVec.ofNat width (xs2.length + 1), r8b, r9b, 0, lb,
      ⟨⟨pre1, by omega⟩, pre2, by omega⟩, ?_, by omega⟩
    simp only [Prod.mk.injEq, true_and, and_true]
    congr 1; simp; omega
  · have hb : (b2w true : BitVec width) ≠ 0 := by
      simp [b2w, b2n, NeZero.ne]
    obtain ⟨w, rfl⟩ : ∃ w, zs4 = [w] := by
      match zs4, hz4 with
      | [w], _ => exact ⟨w, rfl⟩
    have tn : (BitVec.ofNat width (ys.length + xs2.length)).toNat = (qs1 ++ qs2).length := by
      rw [ofNat_toNat_of_lt lb2]; simp; omega
    simp only [hb, if_true, if_false, tn]
    refine ⟨0, BitVec.ofNat width (xs2.length + 1), 1, r9b, 0, lb,
      ⟨⟨⟨pre1, by omega⟩, pre2, by omega⟩, by simp⟩, ?_, by omega⟩
    simp only [Prod.mk.injEq, List.length_append, true_and]
    refine ⟨?_, ?_⟩
    · congr 1; simp; omega
    · rw [show qs1 ++ (qs2 ++ ([w] ++ zs2)) = (qs1 ++ qs2) ++ w :: zs2 by simp,
        show qs1.length + qs2.length = (qs1 ++ qs2).length by simp, set_append_length]
      simp

end Flapjack.Misc.Multiword
