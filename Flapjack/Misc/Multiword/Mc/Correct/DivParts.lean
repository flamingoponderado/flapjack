module

public import Flapjack.Misc.Multiword.Mc.Correct.DivLoop

@[expose] public section

/-! Correctness of the machine-code-style auxiliary passes of HOL's
`mc_multiword` division: multiplication by the normalisation factor, the
divisor's top digits, and the copying loops. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Flapjack proof of the local HOL lemma `mc_mul_by_single_thm` (before its
specialization). -/
theorem mcMulBySingle_thm_gen {width : Nat} [NeZero width] :
    ∀ (xs xs1 : List (BitVec width)) (x : BitVec width) (zs : List (BitVec width))
      (k : BitVec width) (zs1 zs2 : List (BitVec width)) (z2 : BitVec width) (l : Nat),
      (xs1 ++ xs).length < 2 ^ width ∧ zs.length = xs.length ∧
      (zs1 ++ zs).length < 2 ^ width ∧ xs.length ≤ l →
      ∃ r1 l2,
        mcMulBySinglePre (l, k, x, BitVec.ofNat width (xs1 ++ xs).length,
          BitVec.ofNat width zs1.length, BitVec.ofNat width xs1.length, xs1 ++ xs,
          zs1 ++ zs ++ z2 :: zs2) ∧
        mcMulBySingle (l, k, x, BitVec.ofNat width (xs1 ++ xs).length,
          BitVec.ofNat width zs1.length, BitVec.ofNat width xs1.length, xs1 ++ xs,
          zs1 ++ zs ++ z2 :: zs2) =
          (l2, r1, x, BitVec.ofNat width (xs1 ++ xs).length,
            BitVec.ofNat width ((zs1 ++ zs).length + 1), xs1 ++ xs,
            zs1 ++ mwMulPass x xs (xs.map fun _ => 0) k ++ zs2) ∧
        l ≤ l2 + xs.length := by
  intro xs
  induction xs with
  | nil =>
    intro xs1 x zs k zs1 zs2 z2 l ⟨_, hz, h3, _⟩
    rw [List.eq_nil_of_length_eq_zero hz] at h3 ⊢
    simp only [List.append_nil] at h3
    have tz : (BitVec.ofNat width zs1.length).toNat = zs1.length := ofNat_toNat_of_lt h3
    refine ⟨k, l, ?_, ?_, by simp⟩
    · rw [mcMulBySinglePre_def]; simp [tz]
    · rw [mcMulBySingle_def]
      simp only [List.append_nil, if_true, tz, ofNat_add_one, set_append_length]
      simp [mwMulPass]
  | cons y xs ih =>
    intro xs1 x zs k zs1 zs2 z2 l ⟨h1, hz, h3, hl⟩
    obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_length_eq_add_one hz
    simp only [List.length_cons, List.length_append] at hz h1 h3 hl ⊢
    obtain ⟨r1, l2, pre, eq, bound⟩ :=
      ih (xs1 ++ [y]) x zs (singleMulAdd x y k 0).2 (zs1 ++ [(singleMulAdd x y k 0).1]) zs2 z2
        (l - 1) ⟨by simp; omega, by omega, by simp; omega, by omega⟩
    have ne : BitVec.ofNat width (xs1.length + (xs.length + 1)) ≠
        BitVec.ofNat width xs1.length := by
      rw [Ne, ofNat_inj h1 (by omega)]; omega
    have tz : (BitVec.ofNat width zs1.length).toNat = zs1.length := ofNat_toNat_of_lt (by omega)
    have ty : (BitVec.ofNat width xs1.length).toNat = xs1.length := ofNat_toNat_of_lt (by omega)
    have ey : holEl xs1.length (xs1 ++ y :: xs) = y := holEl_append_length xs1 xs y
    have sz : (zs1 ++ z :: zs ++ z2 :: zs2).set zs1.length (singleMulAdd x y k 0).1 =
        zs1 ++ [(singleMulAdd x y k 0).1] ++ zs ++ z2 :: zs2 := by simp
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_singleton] at pre eq sz ⊢
    refine ⟨r1, l2, ?_, ?_, by omega⟩
    · rw [mcMulBySinglePre_def]
      simp only [ne, if_false, tz, ty, ey, mcSingleMulAdd_thm.2, sz, ofNat_add_one]
      refine ⟨by simpa using pre, ⟨⟨by simp, mcSingleMulAdd_thm.1⟩, by simp⟩, by omega⟩
    · rw [mcMulBySingle_def]
      simp only [ne, if_false, tz, ty, ey, mcSingleMulAdd_thm.2, sz, ofNat_add_one]
      simp only [List.length_cons] at eq
      rw [eq]
      simp only [List.map_cons, mwMulPass, holHd, List.tail_cons, List.cons_append,
        Nat.add_assoc]

/-- `k2mw` of a length is a zero list (Flapjack helper). -/
theorem k2mw_length_zero {width : Nat} [NeZero width] (xs : List (BitVec width)) :
    (k2mw xs.length 0 : List (BitVec width)) = xs.map fun _ => 0 := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp [k2mw, ih]

/-- Flapjack proof of the local HOL lemma `mc_mul_by_single_thm`. -/
theorem mcMulBySingle_thm {width : Nat} [NeZero width] :
    ∀ (xs : List (BitVec width)) (x : BitVec width) (zs zs2 : List (BitVec width))
      (z2 : BitVec width) (l : Nat),
      xs.length < 2 ^ width ∧ zs.length = xs.length ∧ zs.length < 2 ^ width ∧ xs.length ≤ l →
      ∃ r1 l2,
        mcMulBySinglePre (l, 0, x, BitVec.ofNat width xs.length, 0, 0, xs, zs ++ z2 :: zs2) ∧
        mcMulBySingle (l, 0, x, BitVec.ofNat width xs.length, 0, 0, xs, zs ++ z2 :: zs2) =
          (l2, r1, x, BitVec.ofNat width xs.length, BitVec.ofNat width (zs.length + 1), xs,
            mwMulBySingle x xs ++ zs2) ∧
        l ≤ l2 + xs.length := by
  intro xs x zs zs2 z2 l h
  have := mcMulBySingle_thm_gen xs [] x zs 0 [] zs2 z2 l (by simpa using h)
  simpa [mwMulBySingle, k2mw_length_zero] using this

/-- Flapjack proof of the local HOL lemma `mc_top_two_thm` (before its
specialization). -/
theorem mcTopTwo_thm_gen {width : Nat} [NeZero width] :
    ∀ (ys : List (BitVec width)) (x k1 k2 k3 : BitVec width) (ys1 : List (BitVec width))
      (l : Nat),
      (ys1 ++ ys).length < 2 ^ width ∧ ys.length ≤ l →
      ∃ l2,
        mcTopTwoPre (l, k2, k1, k3, x, BitVec.ofNat width (ys1 ++ ys).length,
          BitVec.ofNat width ys1.length, ys1 ++ ys) ∧
        mcTopTwo (l, k2, k1, k3, x, BitVec.ofNat width (ys1 ++ ys).length,
          BitVec.ofNat width ys1.length, ys1 ++ ys) =
          (l2, (mwMulPassTop x ys (k1, k2, k3)).2.1, (mwMulPassTop x ys (k1, k2, k3)).2.2, x,
            BitVec.ofNat width (ys1 ++ ys).length, BitVec.ofNat width (ys1 ++ ys).length,
            ys1 ++ ys) ∧
        l ≤ l2 + ys.length := by
  intro ys
  induction ys with
  | nil =>
    intro x k1 k2 k3 ys1 l _
    refine ⟨l, ?_, ?_, by simp⟩
    · rw [mcTopTwoPre_def]; simp
    · rw [mcTopTwo_def]; simp [mwMulPassTop]
  | cons y ys ih =>
    intro x k1 k2 k3 ys1 l ⟨h1, hl⟩
    simp only [List.length_cons, List.length_append] at h1 hl ⊢
    obtain ⟨l2, pre, eq, bound⟩ :=
      ih x (singleMulAdd x y k1 0).2 (singleMulAdd x y k1 0).1 k2 (ys1 ++ [y]) (l - 1)
        ⟨by simp; omega, by omega⟩
    have ne : BitVec.ofNat width (ys1.length + (ys.length + 1)) ≠
        BitVec.ofNat width ys1.length := by
      rw [Ne, ofNat_inj h1 (by omega)]; omega
    have ty : (BitVec.ofNat width ys1.length).toNat = ys1.length := ofNat_toNat_of_lt (by omega)
    have ey : holEl ys1.length (ys1 ++ y :: ys) = y := holEl_append_length ys1 ys y
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_singleton] at pre eq ⊢
    refine ⟨l2, ?_, ?_, by omega⟩
    · rw [mcTopTwoPre_def]
      simp only [ne, if_false, ty, ey, mcSingleMul_thm.2, ofNat_add_one]
      exact ⟨by simpa using pre, ⟨by simp, mcSingleMul_thm.1⟩, by omega⟩
    · rw [mcTopTwo_def]
      simp only [ne, if_false, ty, ey, mcSingleMul_thm.2, ofNat_add_one]
      refine Eq.trans (by simpa using eq) ?_
      simp only [mwMulPassTop]
      rfl

/-- Flapjack proof of the local HOL lemma `mc_top_two_thm`. -/
theorem mcTopTwo_thm {width : Nat} [NeZero width] {ys : List (BitVec width)}
    {x : BitVec width} {l : Nat} :
    1 < ys.length ∧ ys.length < 2 ^ width ∧ ys.length ≤ l →
    ∃ l2,
      mcTopTwoPre (l, 0, 0, 0, x, BitVec.ofNat width ys.length, 0, ys) ∧
      mcTopTwo (l, 0, 0, 0, x, BitVec.ofNat width ys.length, 0, ys) =
        (l2, holLast (mwMulBySingle x ys).dropLast,
          holLast (mwMulBySingle x ys).dropLast.dropLast, x,
          BitVec.ofNat width ys.length, BitVec.ofNat width ys.length, ys) ∧
      l ≤ l2 + ys.length := by
  rintro ⟨h1, h2, h3⟩
  obtain ⟨l2, pre, eq, b⟩ := mcTopTwo_thm_gen ys x 0 0 0 [] l (by simpa using ⟨h2, h3⟩)
  rw [mwMulPassTop_thm h1] at eq
  exact ⟨l2, by simpa using pre, by simpa using eq, by simpa using b⟩

/-- Flapjack proof of the local HOL lemma `mc_copy_down_thm` (before its
specialization). -/
theorem mcCopyDown_thm_gen {width : Nat} [NeZero width] :
    ∀ (zs2 zs0 zs1 zs3 : List (BitVec width)) (l : Nat),
      (zs0 ++ zs1 ++ zs2).length < 2 ^ width ∧ zs1 ≠ [] ∧ zs2.length ≤ l →
      ∃ zs4 l2,
        mcCopyDownPre (l, BitVec.ofNat width zs2.length, BitVec.ofNat width (zs0 ++ zs1).length,
          BitVec.ofNat width zs0.length, zs0 ++ zs1 ++ zs2 ++ zs3) ∧
        mcCopyDown (l, BitVec.ofNat width zs2.length, BitVec.ofNat width (zs0 ++ zs1).length,
          BitVec.ofNat width zs0.length, zs0 ++ zs1 ++ zs2 ++ zs3) =
          (l2, zs0 ++ zs2 ++ zs4) ∧
        zs4.length = zs1.length + zs3.length ∧ l ≤ l2 + zs2.length := by
  intro zs2
  induction zs2 with
  | nil =>
    intro zs0 zs1 zs3 l _
    refine ⟨zs1 ++ zs3, l, by rw [mcCopyDownPre_def]; simp, ?_, by simp, by simp⟩
    rw [mcCopyDown_def]; simp
  | cons h zs2 ih =>
    intro zs0 zs1 zs3 l ⟨hlt, hne, hl⟩
    obtain ⟨z, zs1, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.length_append, List.length_cons] at hlt hl ⊢
    obtain ⟨zs4, l2, pre, eq, len, bound⟩ :=
      ih (zs0 ++ [h]) (zs1 ++ [h]) zs3 (l - 1) ⟨by simp; omega, by simp, by omega⟩
    have ne : BitVec.ofNat width (zs2.length + 1) ≠ 0 := by
      rw [Ne, ofNat_eq_zero (by omega)]; omega
    have sub := ofNat_succ_sub_one (width := width) (n := zs2.length) (by omega)
    have t10 : (BitVec.ofNat width (zs0.length + (zs1.length + 1))).toNat =
        zs0.length + (zs1.length + 1) := ofNat_toNat_of_lt (by omega)
    have t11 : (BitVec.ofNat width zs0.length).toNat = zs0.length := ofNat_toNat_of_lt (by omega)
    have eh : holEl (zs0.length + (zs1.length + 1)) (zs0 ++ z :: zs1 ++ h :: zs2 ++ zs3) = h := by
      have := holEl_append_length (zs0 ++ z :: zs1) (zs2 ++ zs3) h
      simpa using this
    have sz : (zs0 ++ z :: zs1 ++ h :: zs2 ++ zs3).set zs0.length h =
        zs0 ++ [h] ++ (zs1 ++ [h]) ++ zs2 ++ zs3 := by simp
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_cons] at pre eq sz eh len ⊢
    refine ⟨zs4, l2, ?_, ?_, by omega, by omega⟩
    · rw [mcCopyDownPre_def]
      simp only [ne, if_false, sub, t10, t11, eh, sz, ofNat_add_one]
      refine ⟨by simpa [Nat.add_assoc] using pre, ⟨by simp, by simp⟩, by omega⟩
    · rw [mcCopyDown_def]
      simp only [ne, if_false, sub, t10, t11, eh, sz, ofNat_add_one]
      refine Eq.trans (by simpa [Nat.add_assoc] using eq) ?_
      simp

/-- Flapjack proof of the local HOL lemma `mc_copy_down_thm`. -/
theorem mcCopyDown_thm {width : Nat} [NeZero width] :
    ∀ (zs1 zs2 zs3 : List (BitVec width)) (l : Nat),
      (zs1 ++ zs2).length < 2 ^ width ∧ zs1 ≠ [] ∧ zs2.length ≤ l →
      ∃ zs4 l2,
        mcCopyDownPre (l, BitVec.ofNat width zs2.length, BitVec.ofNat width zs1.length, 0,
          zs1 ++ zs2 ++ zs3) ∧
        mcCopyDown (l, BitVec.ofNat width zs2.length, BitVec.ofNat width zs1.length, 0,
          zs1 ++ zs2 ++ zs3) = (l2, zs2 ++ zs4) ∧
        zs4.length = zs1.length + zs3.length ∧ l ≤ l2 + zs2.length := by
  intro zs1 zs2 zs3 l h
  simpa using mcCopyDown_thm_gen zs2 [] zs1 zs3 l (by simpa using h)

/-- Flapjack proof of the local HOL lemma `mc_copy_over_thm`. -/
theorem mcCopyOver_thm {width : Nat} [NeZero width] :
    ∀ (xs0 zs0 xs zs : List (BitVec width)) (l : Nat),
      zs0.length = xs0.length ∧ (zs0 ++ zs).length < 2 ^ width ∧ xs0.length ≤ l →
      ∃ l2,
        mcCopyOverPre (l, BitVec.ofNat width xs0.length, xs0 ++ xs, zs0 ++ zs) ∧
        mcCopyOver (l, BitVec.ofNat width xs0.length, xs0 ++ xs, zs0 ++ zs) =
          (l2, xs0 ++ xs, xs0 ++ zs) ∧ l ≤ l2 + xs0.length := by
  intro xs0
  induction xs0 using snoc_induction with
  | nil =>
    intro zs0 xs zs l ⟨hz, _, _⟩
    rw [List.eq_nil_of_length_eq_zero hz]
    exact ⟨l, by rw [mcCopyOverPre_def]; simp, by rw [mcCopyOver_def]; simp, by simp⟩
  | snoc xs0 x ih =>
    intro zs0 xs zs l ⟨hz, hlt, hl⟩
    obtain ⟨zs0, z, rfl⟩ : ∃ zs0' z, zs0 = zs0' ++ [z] := by
      rcases List.eq_nil_or_concat zs0 with e | ⟨L, b, e⟩
      · subst e; simp at hz
      · exact ⟨L, b, by simpa using e⟩
    simp only [List.length_append, List.length_singleton] at hz hlt hl ⊢
    obtain ⟨l2, pre, eq, bound⟩ := ih zs0 (x :: xs) (x :: zs) (l - 1) ⟨by omega, by simp; omega,
      by omega⟩
    have ne : BitVec.ofNat width (xs0.length + 1) ≠ 0 := by
      rw [Ne, ofNat_eq_zero (by omega)]; omega
    have sub := ofNat_succ_sub_one (width := width) (n := xs0.length) (by omega)
    have tn : (BitVec.ofNat width xs0.length).toNat = xs0.length := ofNat_toNat_of_lt (by omega)
    have ex' : holEl xs0.length (xs0 ++ x :: xs) = x := holEl_append_length xs0 xs x
    have sz' : (zs0 ++ z :: zs).set xs0.length x = zs0 ++ x :: zs := by
      rw [show xs0.length = zs0.length by omega]; simp
    simp only [List.append_assoc, List.singleton_append] at pre eq ⊢
    refine ⟨l2, ?_, ?_, by omega⟩
    · rw [mcCopyOverPre_def]
      simp only [ne, if_false, sub, tn, ex', sz']
      exact ⟨pre, ⟨by simp, by simp; omega⟩, by omega⟩
    · rw [mcCopyOver_def]
      simp only [ne, if_false, sub, tn, ex', sz', eq]

end Flapjack.Misc.Multiword
