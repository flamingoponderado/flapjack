module

public import Flapjack.Misc.Multiword.Mc.Correct.Iadd

@[expose] public section

/-! Correctness of the machine-code-style multiplication of HOL's
`mc_multiword`. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- The digits of a two-word value are unique (Flapjack helper). -/
theorem two_digits_unique {B a b N : Nat} (ha : a < B) (h : a + B * b = N) :
    a = N % B ∧ b = N / B := by
  subst h
  have hB : 0 < B := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  · rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt ha, Nat.zero_add]

/-- The value of a single-word multiplication (Flapjack helper). -/
theorem singleMul_value {width : Nat} [NeZero width] (x y k : BitVec width) :
    (singleMul x y k).1.toNat + 2 ^ width * (singleMul x y k).2.toNat =
      x.toNat * y.toNat + k.toNat := by
  rcases h : singleMul x y k with ⟨z, l⟩
  simp only [singleMul, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hw : 0 < 2 ^ width := Nat.two_pow_pos _
  have hx := x.isLt
  have hy := y.isLt
  have hk := k.isLt
  have prod : x.toNat * y.toNat ≤ (2 ^ width - 1) * (2 ^ width - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have sq : (2 ^ width - 1) * (2 ^ width - 1) + 2 * (2 ^ width - 1) < 2 ^ width * 2 ^ width := by
    obtain ⟨a, ha⟩ : ∃ a, 2 ^ width = a + 1 := ⟨2 ^ width - 1, by omega⟩
    rw [ha, Nat.add_sub_cancel]
    have : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
    omega
  have small : (x.toNat * y.toNat + k.toNat) / 2 ^ width < 2 ^ width :=
    (Nat.div_lt_iff_lt_mul hw).mpr (by omega)
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Nat.mod_add_mod]
  exact Nat.mod_add_div _ _

/-- Flapjack proof of the local HOL lemma `mc_single_mul_add_thm`. -/
theorem mcSingleMulAdd_thm {width : Nat} [NeZero width] {p k q s : BitVec width} :
    mcSingleMulAddPre (p, k, q, s) ∧
      mcSingleMulAdd (p, k, q, s) =
        ((singleMulAdd p q k s).1, k, (singleMulAdd p q k s).2, s) := by
  refine ⟨by rw [mcSingleMulAddPre_def]; trivial, ?_⟩
  rw [mcSingleMulAdd_def]
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
  rcases hd : singleAdd r0b s false with ⟨r0c, cb⟩
  have a3 := singleAdd_thm r0b s r0c false cb hd
  rcases he : singleAdd r2b 0 cb with ⟨r2c, d2⟩
  have a4 := singleAdd_thm r2b 0 r2c cb d2 he
  rcases hs : singleMulAdd p q k s with ⟨x1, x2⟩
  have spec := singleMulAdd_thm p q k s x1 x2 hs
  have hw : 0 < 2 ^ width := Nat.two_pow_pos _
  have hp := p.isLt
  have hq := q.isLt
  have hk := k.isLt
  have hs' := s.isLt
  have prod : p.toNat * q.toNat ≤ (2 ^ width - 1) * (2 ^ width - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have sq : (2 ^ width - 1) * (2 ^ width - 1) + 2 * (2 ^ width - 1) < 2 ^ width * 2 ^ width := by
    obtain ⟨a, ha⟩ : ∃ a, 2 ^ width = a + 1 := ⟨2 ^ width - 1, by omega⟩
    rw [ha, Nat.add_sub_cancel]
    have : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
    omega
  have z0 : (0 : BitVec width).toNat = 0 := by simp
  rw [z0, Nat.add_zero] at a2 a4 mul
  have s2 := congrArg (2 ^ width * ·) a2
  have s4 := congrArg (2 ^ width * ·) a4
  simp only [Nat.mul_add, ← Nat.mul_assoc] at s2 s4
  have total : r0c.toNat + 2 ^ width * r2c.toNat = x1.toNat + 2 ^ width * x2.toNat := by
    cases ca <;> cases d1 <;> cases cb <;> cases d2 <;>
      simp only [b2n, Nat.mul_one, Nat.mul_zero, Nat.add_zero] at a1 a2 a3 a4 s2 s4 <;> omega
  have u1 := two_digits_unique r0c.isLt total
  have u2 := two_digits_unique (b := x2.toNat) x1.isLt rfl
  have e1 : r0c = x1 := BitVec.eq_of_toNat_eq (by rw [u1.1, ← u2.1])
  have e2 : r2c = x2 := BitVec.eq_of_toNat_eq (by
    have := u1.2; rw [this]; exact u2.2.symm)
  rw [e1, e2]

/-- Flapjack proof of the local HOL lemma `mc_mul_pass_thm` (before its
specialization to an empty prefix of `ys`). -/
theorem mcMulPass_thm_gen {width : Nat} [NeZero width] :
    ∀ (ys ys1 : List (BitVec width)) (x : BitVec width) (zs : List (BitVec width))
      (k : BitVec width) (zs1 zs2 : List (BitVec width)) (z2 : BitVec width) (l : Nat),
      (ys1 ++ ys).length < 2 ^ width ∧ zs.length = ys.length ∧
      (zs1 ++ zs).length < 2 ^ width ∧ ys.length ≤ l →
      ∃ r1 l2,
        mcMulPassPre (l, k, x, BitVec.ofNat width (ys1 ++ ys).length,
          BitVec.ofNat width zs1.length, BitVec.ofNat width ys1.length, ys1 ++ ys,
          zs1 ++ zs ++ z2 :: zs2) ∧
        mcMulPass (l, k, x, BitVec.ofNat width (ys1 ++ ys).length,
          BitVec.ofNat width zs1.length, BitVec.ofNat width ys1.length, ys1 ++ ys,
          zs1 ++ zs ++ z2 :: zs2) =
          (l2, r1, BitVec.ofNat width (ys1 ++ ys).length,
            BitVec.ofNat width ((zs1 ++ zs).length + 1), ys1 ++ ys,
            zs1 ++ mwMulPass x ys zs k ++ zs2) ∧
        l ≤ l2 + ys.length := by
  intro ys
  induction ys with
  | nil =>
    intro ys1 x zs k zs1 zs2 z2 l ⟨_, hz, h3, _⟩
    rw [List.eq_nil_of_length_eq_zero hz] at h3 ⊢
    simp only [List.append_nil] at h3
    have tz : (BitVec.ofNat width zs1.length).toNat = zs1.length := ofNat_toNat_of_lt h3
    refine ⟨k, l, ?_, ?_, by simp⟩
    · rw [mcMulPassPre_def]; simp [tz]
    · rw [mcMulPass_def]
      simp only [List.append_nil, if_true, tz, ofNat_add_one, set_append_length]
      simp [mwMulPass]
  | cons y ys ih =>
    intro ys1 x zs k zs1 zs2 z2 l ⟨h1, hz, h3, hl⟩
    obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_length_eq_add_one hz
    simp only [List.length_cons, List.length_append] at hz h1 h3 hl ⊢
    obtain ⟨r1, l2, pre, eq, bound⟩ :=
      ih (ys1 ++ [y]) x zs (singleMulAdd x y k z).2 (zs1 ++ [(singleMulAdd x y k z).1]) zs2 z2 (l - 1)
        ⟨by simp; omega, by omega, by simp; omega, by omega⟩
    have ne : BitVec.ofNat width (ys1.length + (ys.length + 1)) ≠ BitVec.ofNat width ys1.length := by
      rw [Ne, ofNat_inj h1 (by omega)]; omega
    have tz : (BitVec.ofNat width zs1.length).toNat = zs1.length := ofNat_toNat_of_lt (by omega)
    have ty : (BitVec.ofNat width ys1.length).toNat = ys1.length := ofNat_toNat_of_lt (by omega)
    have ez : holEl zs1.length (zs1 ++ z :: zs ++ z2 :: zs2) = z := by
      simpa using holEl_append_length zs1 (zs ++ z2 :: zs2) z
    have ey : holEl ys1.length (ys1 ++ y :: ys) = y := holEl_append_length ys1 ys y
    have sz : (zs1 ++ z :: zs ++ z2 :: zs2).set zs1.length (singleMulAdd x y k z).1 =
        zs1 ++ [(singleMulAdd x y k z).1] ++ zs ++ z2 :: zs2 := by simp
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_singleton] at pre eq sz ez ⊢
    refine ⟨r1, l2, ?_, ?_, by omega⟩
    · rw [mcMulPassPre_def]
      simp only [ne, if_false, tz, ty, ez, ey, mcSingleMulAdd_thm.2, sz, ofNat_add_one]
      refine ⟨by simpa using pre, ⟨⟨by simp, by simp⟩, mcSingleMulAdd_thm.1⟩, by omega⟩
    · rw [mcMulPass_def]
      simp only [ne, if_false, tz, ty, ez, ey, mcSingleMulAdd_thm.2, sz, ofNat_add_one]
      simp only [List.length_cons] at eq
      rw [eq]
      simp only [mwMulPass, holHd, List.tail_cons, List.cons_append, Nat.add_assoc]

/-- Flapjack proof of the local HOL lemma `mc_mul_pass_thm`. -/
theorem mcMulPass_thm {width : Nat} [NeZero width] :
    ∀ (ys : List (BitVec width)) (x : BitVec width) (zs : List (BitVec width))
      (k : BitVec width) (zs1 zs2 : List (BitVec width)) (z2 : BitVec width) (l : Nat),
      ys.length < 2 ^ width ∧ zs.length = ys.length ∧
      (zs1 ++ zs).length < 2 ^ width ∧ ys.length ≤ l →
      ∃ r1 l2,
        mcMulPassPre (l, k, x, BitVec.ofNat width ys.length,
          BitVec.ofNat width zs1.length, 0, ys, zs1 ++ zs ++ z2 :: zs2) ∧
        mcMulPass (l, k, x, BitVec.ofNat width ys.length,
          BitVec.ofNat width zs1.length, 0, ys, zs1 ++ zs ++ z2 :: zs2) =
          (l2, r1, BitVec.ofNat width ys.length,
            BitVec.ofNat width ((zs1 ++ zs).length + 1), ys,
            zs1 ++ mwMulPass x ys zs k ++ zs2) ∧
        l ≤ l2 + ys.length := by
  intro ys x zs k zs1 zs2 z2 l h
  simpa using mcMulPass_thm_gen ys [] x zs k zs1 zs2 z2 l (by simpa using h)

/-- Flapjack proof of the local HOL lemma `mc_mul_thm` (before its
specialization to empty prefixes). -/
theorem mcMul_thm_gen {width : Nat} [NeZero width] :
    ∀ (xs ys zs xs1 zs1 zs2 : List (BitVec width)) (l : Nat),
      (xs1 ++ xs).length < 2 ^ width ∧ ys.length < 2 ^ width ∧ zs.length = ys.length ∧
      (zs1 ++ zs ++ zs2).length < 2 ^ width ∧ xs.length ≤ zs2.length ∧ ys ≠ [] ∧
      2 * xs.length + xs.length * ys.length ≤ l →
      ∃ zs3 l2,
        mcMulPre (l, BitVec.ofNat width xs.length, BitVec.ofNat width ys.length,
          BitVec.ofNat width zs1.length, BitVec.ofNat width xs1.length, xs1 ++ xs, ys,
          zs1 ++ zs ++ zs2) ∧
        mcMul (l, BitVec.ofNat width xs.length, BitVec.ofNat width ys.length,
          BitVec.ofNat width zs1.length, BitVec.ofNat width xs1.length, xs1 ++ xs, ys,
          zs1 ++ zs ++ zs2) =
          (l2, BitVec.ofNat width (zs1 ++ mwMul xs ys zs).length, xs1 ++ xs, ys,
            zs1 ++ mwMul xs ys zs ++ zs3) ∧
        (zs1 ++ zs ++ zs2).length = (zs1 ++ mwMul xs ys zs ++ zs3).length ∧
        l ≤ l2 + 2 * xs.length + xs.length * ys.length := by
  intro xs
  induction xs with
  | nil =>
    intro ys zs xs1 zs1 zs2 l ⟨_, _, hz, _, _, _, _⟩
    refine ⟨zs2, l, by rw [mcMulPre_def]; simp, ?_, by simp [mwMul], by simp⟩
    rw [mcMul_def]
    simp only [List.length_nil, List.append_nil, mwMul]
    have z0 : (BitVec.ofNat width 0 : BitVec width) = 0 := rfl
    rw [z0, if_pos rfl, BitVec.add_def]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp [hz]
  | cons x xs ih =>
    intro ys zs xs1 zs1 zs2 l ⟨h1, hy, hz, h4, h5, hne, hl⟩
    simp only [List.length_cons, List.length_append] at h1 h4 h5 hl ⊢
    obtain ⟨z2, zs2, rfl⟩ : ∃ z2 zs2', zs2 = z2 :: zs2' := by
      cases zs2 with
      | nil => simp at h5
      | cons a b => exact ⟨a, b, rfl⟩
    simp only [List.length_cons] at h4 h5
    have hmul : (xs.length + 1) * ys.length = xs.length * ys.length + ys.length := by ring
    obtain ⟨r1, la, pre1, eq1, bound1⟩ :=
      mcMulPass_thm ys x zs 0 zs1 zs2 z2 (l - 1) ⟨hy, hz, by simp; omega, by omega⟩
    have lp := length_mwMulPass ys zs x 0
    obtain ⟨h, t, ht⟩ : ∃ h t, mwMulPass x ys zs 0 = h :: t := by
      cases e : mwMulPass x ys zs 0 with
      | nil => rw [e] at lp; simp at lp
      | cons a b => exact ⟨a, b, rfl⟩
    rw [ht] at lp eq1
    simp only [List.length_cons] at lp
    obtain ⟨zs3, lb, pre2, eq2, len2, bound2⟩ :=
      ih ys t (xs1 ++ [x]) (zs1 ++ [h]) zs2 (la - 1)
        ⟨by simp; omega, hy, by omega, by simp; omega, by omega, hne, by omega⟩
    have ne : BitVec.ofNat width (xs.length + 1) ≠ 0 := by
      rw [Ne, ofNat_eq_zero (by omega)]; omega
    have sub := ofNat_succ_sub_one (width := width) (n := xs.length) (by omega)
    have tx : (BitVec.ofNat width xs1.length).toNat = xs1.length := ofNat_toNat_of_lt (by omega)
    have ex : holEl xs1.length (xs1 ++ x :: xs) = x := holEl_append_length xs1 xs x
    have z0 : (BitVec.ofNat width 0 : BitVec width) = 0 := rfl
    have sub2 : BitVec.ofNat width (zs1.length + zs.length + 1) - BitVec.ofNat width ys.length =
        BitVec.ofNat width (zs1.length + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ofNat_toNat_of_lt (by omega),
        ofNat_toNat_of_lt (by omega)]; omega), ofNat_toNat_of_lt (by omega),
        ofNat_toNat_of_lt (by omega), ofNat_toNat_of_lt (by omega)]
      omega
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_cons] at pre1 eq1 pre2 eq2 len2 ⊢
    refine ⟨zs3, lb, ?_, ?_, ?_, by omega⟩
    · rw [mcMulPre_def]
      simp only [ne, if_false, sub, tx, ex, ofNat_add_one, eq1, sub2]
      exact ⟨pre2, ⟨by simp, pre1, by omega⟩, by omega⟩
    · rw [mcMul_def]
      simp only [ne, if_false, sub, tx, ex, ofNat_add_one, eq1, sub2]
      refine Eq.trans eq2 ?_
      simp only [mwMul, ht, holHd, List.tail_cons, List.length_cons, List.cons_append]
    · simp only [mwMul, ht, holHd, List.tail_cons, List.length_cons]
      omega

/-- Flapjack proof of the local HOL lemma `mc_mul_zero_thm`. -/
theorem mcMulZero_thm {width : Nat} [NeZero width] :
    ∀ (zs zs1 : List (BitVec width)) (l : Nat),
      zs.length < 2 ^ width ∧ zs.length ≤ l →
      mcMulZeroPre (l, 0, BitVec.ofNat width zs.length, zs ++ zs1) ∧
      mcMulZero (l, 0, BitVec.ofNat width zs.length, zs ++ zs1) =
        (l - zs.length, 0, zs.map (fun _ => (0 : BitVec width)) ++ zs1) := by
  intro zs
  induction zs using snoc_induction with
  | nil =>
    intro zs1 l _
    exact ⟨by rw [mcMulZeroPre_def]; simp, by rw [mcMulZero_def]; simp⟩
  | snoc zs x ih =>
    intro zs1 l ⟨hlt, hle⟩
    simp only [List.length_append, List.length_singleton] at hlt hle ⊢
    have ne : BitVec.ofNat width (zs.length + 1) ≠ 0 := by
      rw [Ne, ofNat_eq_zero hlt]; omega
    have sub := ofNat_succ_sub_one (width := width) (n := zs.length) hlt
    have tn : (BitVec.ofNat width zs.length).toNat = zs.length := ofNat_toNat_of_lt (by omega)
    have sz : (zs ++ [x] ++ zs1).set zs.length 0 = zs ++ (0 :: zs1) := by simp
    obtain ⟨pre, eq⟩ := ih (0 :: zs1) (l - 1) ⟨by omega, by omega⟩
    rw [mcMulZeroPre_def, mcMulZero_def]
    simp only [ne, if_false, sub, tn, sz]
    refine ⟨⟨pre, by simp, by omega⟩, ?_⟩
    rw [eq]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.singleton_append]
    congr 1; omega

/-- Flapjack proof of the local HOL lemma `MAP_EQ_MAP_EQ`. -/
theorem map_zero_eq_map_zero {width : Nat} :
    ∀ (xs ys : List (BitVec width)),
      (xs.map (fun _ => (0 : BitVec width)) = ys.map (fun _ => (0 : BitVec width))) ↔
        xs.length = ys.length := by
  intro xs
  induction xs with
  | nil => intro ys; cases ys <;> simp
  | cons x xs ih =>
    intro ys
    cases ys with
    | nil => simp
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq, true_and, List.length_cons, ih]
      omega

/-- Flapjack proof of the local HOL lemma `mc_imul1_thm`. -/
theorem mcImul1_thm {width : Nat} [NeZero width] {r10 r11 : BitVec width} :
    mcImul1Pre (r10, r11) ∧
      mcImul1 (r10, r11) = (r10, r11, if r10 = r11 then 0 else 1) := by
  refine ⟨?_, ?_⟩
  · rw [mcImul1Pre_def]; split <;> trivial
  · rw [mcImul1_def]; split <;> rfl

/-- The sign word of a product (Flapjack helper). -/
theorem b2w_ne_sign {width : Nat} [NeZero width] (s t : Bool) :
    (if (b2w s : BitVec width) = b2w t then 0 else 1) = (b2w (decide (s ≠ t)) : BitVec width) := by
  cases s <;> cases t <;> simp [b2w, b2n, NeZero.ne]

/-- Flapjack proof of the local HOL lemma `mc_imul_thm`. -/
theorem mcImul_thm {width : Nat} [NeZero width] {s t : Bool} {xs ys zs : List (BitVec width)}
    {l : Nat} :
    ((mcHeader (s, xs) = 0) ↔ xs = []) ∧ ((mcHeader (t, ys) = 0) ↔ ys = []) ∧
    xs.length < 2 ^ width / 2 ∧ ys.length < 2 ^ width / 2 ∧
    xs.length + ys.length ≤ zs.length ∧ zs.length < 2 ^ width / 2 ∧
    3 * xs.length + 3 * ys.length + xs.length * ys.length + 3 ≤ l →
    ∃ zs1 l2,
      mcImulPre (l, mcHeader (s, xs), mcHeader (t, ys), xs, ys, zs) ∧
      mcImul (l, mcHeader (s, xs), mcHeader (t, ys), xs, ys, zs) =
        (l2, mcHeader (mwiMul (s, xs) (t, ys)), xs, ys, (mwiMul (s, xs) (t, ys)).2 ++ zs1) ∧
      ((mwiMul (s, xs) (t, ys)).2 ++ zs1).length = zs.length ∧
      l ≤ l2 + 3 * xs.length + 3 * ys.length + xs.length * ys.length + 3 := by
  rintro ⟨h0x, h0y, hx, hy, hz, hzs, hl⟩
  have hx' := lt_half_succ hx
  have hy' := lt_half_succ hy
  rw [mcImulPre_def, mcImul_def]
  by_cases ex : xs = []
  · subst ex
    simp only [h0x.mpr rfl, if_true]
    refine ⟨zs, l, trivial, ?_, by simp [mwiMul], by omega⟩
    simp [mwiMul, mcHeader]
  by_cases ey : ys = []
  · subst ey
    simp only [h0y.mpr rfl, if_true, (h0x.not).mpr ex, if_false]
    refine ⟨zs, l, trivial, ?_, by simp [mwiMul], by omega⟩
    simp [mwiMul, mcHeader]
  simp only [(h0x.not).mpr ex, (h0y.not).mpr ey, if_false, mc_length hx, mc_length hy,
    mcHeader_AND_1, mcImul1_thm.2, b2w_ne_sign]
  obtain ⟨qs1, qs2, rfl, hq1⟩ := less_eq_length zs ys.length (by omega)
  simp only [List.length_append] at hz hzs
  obtain ⟨pz, ez⟩ := mcMulZero_thm qs1 qs2 (l - 1) ⟨by omega, by omega⟩
  rw [hq1] at pz ez
  have mz : qs1.map (fun _ => (0 : BitVec width)) = ys.map (fun _ => (0 : BitVec width)) :=
    (map_zero_eq_map_zero qs1 ys).mpr hq1
  rw [mz] at ez
  have hxy : xs.length * ys.length ≥ 0 := Nat.zero_le _
  obtain ⟨zs3, l3, pm, em, lm, bm⟩ :=
    mcMul_thm_gen xs ys (ys.map fun _ => 0) [] [] qs2 (l - 1 - ys.length - 1)
      ⟨by simp; omega, by omega, by simp, by simp; omega, by omega, ey, by omega⟩
  simp only [List.nil_append, List.length_nil] at pm em lm
  have z0 : (BitVec.ofNat width 0 : BitVec width) = 0 := rfl
  rw [z0] at pm em
  have lM := length_mwMul xs ys (ys.map fun _ => 0) (by simp)
  obtain ⟨r8', l4, pf, ef, bf⟩ :=
    mcFix_thm (mwMul xs ys (ys.map fun _ => 0)) zs3 0 (l3 - 1) ⟨by omega, by omega⟩
  simp only [ez, em, ef]
  refine ⟨List.replicate ((mwMul xs ys (ys.map fun _ => 0)).length -
      (mwFix (mwMul xs ys (ys.map fun _ => 0))).length) 0 ++ zs3, l4,
    ⟨⟨⟨pz, by omega⟩, pm, by omega⟩, pf, by omega⟩, ?_, ?_, by omega⟩
  · simp only [mwiMul, ex, ey, or_self, if_false, shift_add_b2w, List.append_assoc]
    congr
  · have := length_mwFix (mwMul xs ys (ys.map fun _ => 0))
    simp only [mwiMul, ex, ey, or_self, if_false, List.length_append, List.length_replicate,
      List.length_map] at lm ⊢
    omega

end Flapjack.Misc.Multiword
