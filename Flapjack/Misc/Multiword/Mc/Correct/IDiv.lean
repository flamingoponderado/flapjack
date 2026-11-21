module

public import Flapjack.Misc.Multiword.Mc.Correct.Div
public import Flapjack.Misc.Multiword.Mc.IDiv

@[expose] public section

/-! Correctness of the machine-code-style signed division of HOL's
`mc_multiword` (the local HOL lemma `mc_idiv_thm`). -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Flapjack proof of the local HOL lemma `mw_addv_NIL_F`. -/
theorem mwAddv_nil_false {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width), mwAddv xs [] false = xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := x.isLt
    simp only [mwAddv, if_true, singleAdd, b2w, b2n]
    have z : (0 : BitVec width).toNat = 0 := by simp
    simp only [List.cons.injEq]
    refine ⟨by apply BitVec.eq_of_toNat_eq; simp, ?_⟩
    simp only [z, Nat.add_zero]
    rw [decide_eq_false (by omega)]
    exact ih

/-- Flapjack proof of the local HOL lemma `mw_addv_CONS_NIL_T`. -/
theorem mwAddv_cons_nil_true {width : Nat} [NeZero width] (x : BitVec width)
    (xs : List (BitVec width)) :
    mwAddv (x :: xs) [] true =
      if x = ~~~0 then 0 :: mwAddv xs [] true else (x + 1) :: xs := by
  have hx := x.isLt
  have h1 : (1 : Nat) < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  have z : (0 : BitVec width).toNat = 0 := by simp
  have one : (BitVec.ofNat width 1 : BitVec width).toNat = 1 := by simp [Nat.mod_eq_of_lt h1]
  have nt : (~~~(0 : BitVec width)).toNat = 2 ^ width - 1 := by simp
  simp only [mwAddv, if_true, singleAdd, b2w, b2n, z, Nat.add_zero]
  by_cases hm : x = ~~~0
  · subst hm
    rw [if_pos rfl, nt, decide_eq_true (by omega)]
    simp only [List.cons.injEq, and_true]
    apply BitVec.eq_of_toNat_eq
    simp [Nat.sub_add_cancel (Nat.one_le_two_pow)]
  · rw [if_neg hm]
    have : x.toNat ≠ 2 ^ width - 1 := fun e => hm (BitVec.eq_of_toNat_eq (by rw [e, nt]))
    rw [decide_eq_false (by omega), mwAddv_nil_false]
    simp only [List.cons.injEq, and_true]
    apply BitVec.eq_of_toNat_eq
    simp [one]

/-- Flapjack proof of the local HOL lemma `mc_add1_thm` (before its
specialization). -/
theorem mcAdd1_thm_gen {width : Nat} [NeZero width] {zs2 : List (BitVec width)} :
    ∀ (zs zs1 : List (BitVec width)) (l : Nat),
      (zs1 ++ zs).length + 1 < 2 ^ width ∧ zs2 ≠ [] ∧ zs.length ≤ l →
      ∃ rest l2,
        mcAdd1Pre (l, ~~~0, BitVec.ofNat width zs1.length, BitVec.ofNat width (zs1 ++ zs).length,
          zs1 ++ zs ++ zs2) ∧
        mcAdd1 (l, ~~~0, BitVec.ofNat width zs1.length, BitVec.ofNat width (zs1 ++ zs).length,
          zs1 ++ zs ++ zs2) =
          (l2, BitVec.ofNat width (zs1 ++ mwAddv zs [] true).length,
            zs1 ++ mwAddv zs [] true ++ rest) ∧
        (zs1 ++ mwAddv zs [] true).length < 2 ^ width ∧
        (zs1 ++ mwAddv zs [] true ++ rest).length = (zs1 ++ zs ++ zs2).length ∧
        l ≤ l2 + zs.length := by
  intro zs
  induction zs with
  | nil =>
    intro zs1 l ⟨hlt, hne, _⟩
    obtain ⟨t, zs2', rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.append_nil, List.length_append] at hlt ⊢
    have tz : (BitVec.ofNat width zs1.length).toNat = zs1.length := ofNat_toNat_of_lt (by omega)
    refine ⟨zs2', l, ?_, ?_, ?_, ?_, by simp⟩
    · rw [mcAdd1Pre_def]; simp [tz]
    · rw [mcAdd1_def]; simp [tz, mwAddv]; exact ofNat_add_one _
    · simp [mwAddv]; omega
    · simp [mwAddv]; omega
  | cons h zs ih =>
    intro zs1 l ⟨hlt, hne, hl⟩
    simp only [List.length_append, List.length_cons] at hlt hl ⊢
    have ne : BitVec.ofNat width zs1.length ≠ BitVec.ofNat width (zs1.length + (zs.length + 1)) := by
      rw [Ne, ofNat_inj (by omega) (by omega)]; omega
    have tz : (BitVec.ofNat width zs1.length).toNat = zs1.length := ofNat_toNat_of_lt (by omega)
    have eh : holEl zs1.length (zs1 ++ h :: zs ++ zs2) = h := by
      simpa using holEl_append_length zs1 (zs ++ zs2) h
    rw [mcAdd1Pre_def, mcAdd1_def, mwAddv_cons_nil_true]
    simp only [ne, if_false, tz, eh]
    by_cases hm : h = ~~~0
    · subst hm
      obtain ⟨rest, l2, pre, eq, lt, len, bound⟩ :=
        ih (zs1 ++ [0]) (l - 1) ⟨by simp; omega, hne, by omega⟩
      have sz : (zs1 ++ ~~~0 :: zs ++ zs2).set zs1.length 0 = zs1 ++ [0] ++ zs ++ zs2 := by simp
      simp only [List.append_assoc, List.cons_append, List.nil_append,
        List.length_append, List.length_cons] at pre eq lt len sz ⊢
      simp only [if_true, sz, ofNat_add_one]
      refine ⟨rest, l2, ⟨by simpa [Nat.add_assoc] using pre, by simp, by omega⟩, ?_, ?_, ?_,
        by omega⟩
      · refine Eq.trans (by simpa [Nat.add_assoc] using eq) ?_
        simp
      · simp only [List.length_cons] at lt ⊢; omega
      · simp only [List.length_cons] at len ⊢; omega
    · simp only [hm, if_false]
      refine ⟨zs2, l, by simp, ?_, ?_, ?_, by omega⟩
      · simp
      · simp; omega
      · simp

/-- Flapjack proof of the local HOL lemma `mc_add1_thm`. -/
theorem mcAdd1_thm {width : Nat} [NeZero width] {zs2 : List (BitVec width)} :
    ∀ (zs : List (BitVec width)) (l : Nat),
      zs.length + 1 < 2 ^ width ∧ zs2 ≠ [] ∧ zs.length ≤ l →
      ∃ rest l2,
        mcAdd1Pre (l, ~~~0, 0, BitVec.ofNat width zs.length, zs ++ zs2) ∧
        mcAdd1 (l, ~~~0, 0, BitVec.ofNat width zs.length, zs ++ zs2) =
          (l2, BitVec.ofNat width (mwAddv zs [] true).length, mwAddv zs [] true ++ rest) ∧
        (mwAddv zs [] true).length < 2 ^ width ∧
        (mwAddv zs [] true ++ rest).length = (zs ++ zs2).length ∧
        l ≤ l2 + zs.length := by
  intro zs l h
  simpa using mcAdd1_thm_gen (zs2 := zs2) zs [] l (by simpa using h)

/-- Flapjack proof of the local HOL lemma `mc_div_sub_aux_thm` (before its
specialization; HOL's unused existential flag variables are omitted). -/
theorem mcDivSubAux1_thm_gen {width : Nat} [NeZero width] :
    ∀ (ys zs ys1 zs1 ys2 zs2 : List (BitVec width)) (c : Bool) (r8 r9 : BitVec width)
      (l : Nat),
      zs1.length = ys1.length ∧ zs.length = ys.length ∧
      (zs1 ++ zs).length + 1 < 2 ^ width ∧ ys.length ≤ l →
      ∃ r8' r9' l2,
        mcDivSubAux1Pre (l, BitVec.ofNat width (zs.length + 1), b2w c, r8, r9,
          BitVec.ofNat width zs1.length, ys1 ++ ys ++ ys2, zs1 ++ zs ++ zs2) ∧
        mcDivSubAux1 (l, BitVec.ofNat width (zs.length + 1), b2w c, r8, r9,
          BitVec.ofNat width zs1.length, ys1 ++ ys ++ ys2, zs1 ++ zs ++ zs2) =
          (l2, 0, b2w (mwSub ys zs c).2, r8', r9', BitVec.ofNat width (zs1 ++ zs).length,
            ys1 ++ ys ++ ys2, zs1 ++ (mwSub ys zs c).1 ++ zs2) ∧
        l ≤ l2 + ys.length := by
  intro ys
  induction ys with
  | nil =>
    intro zs ys1 zs1 ys2 zs2 c r8 r9 l ⟨_, h4, _, _⟩
    rw [List.eq_nil_of_length_eq_zero h4]
    refine ⟨r8, r9, l, ?_, ?_, by simp⟩
    · rw [mcDivSubAux1Pre_def]; simp
    · rw [mcDivSubAux1_def]; simp [mwSub]
  | cons y ys ih =>
    intro zs ys1 zs1 ys2 zs2 c r8 r9 l ⟨h1, h4, h5, h6⟩
    obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_length_eq_add_one h4
    simp only [List.length_cons, List.length_append] at h4 h5 h6 ⊢
    obtain ⟨r8', r9', l2, pre, eq, bound⟩ :=
      ih zs (ys1 ++ [y]) (zs1 ++ [(singleSub y z c).1]) ys2 zs2 (singleSub y z c).2
        (singleSub y z c).1 z (l - 1)
        ⟨by simp; omega, by omega, by simp; omega, by omega⟩
    have ne : BitVec.ofNat width (zs.length + 1 + 1) ≠ 1 := by
      rw [Ne, ofNat_succ_eq_one (by omega)]; omega
    have sub := ofNat_succ_sub_one (width := width) (n := zs.length + 1) (by omega)
    have tn : (BitVec.ofNat width zs1.length).toNat = zs1.length := ofNat_toNat_of_lt (by omega)
    have ey : holEl zs1.length (ys1 ++ y :: ys ++ ys2) = y := by
      rw [h1]; simpa using holEl_append_length ys1 (ys ++ ys2) y
    have ez : holEl zs1.length (zs1 ++ z :: zs ++ zs2) = z := by
      simpa using holEl_append_length zs1 (zs ++ zs2) z
    have sz : (zs1 ++ z :: zs ++ zs2).set zs1.length (singleSub y z c).1 =
        zs1 ++ [(singleSub y z c).1] ++ zs ++ zs2 := by simp
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_singleton] at pre eq sz ey ez ⊢
    refine ⟨r8', r9', l2, ?_, ?_, by omega⟩
    · rw [mcDivSubAux1Pre_def]
      simp only [ne, if_false, sub, tn, ey, ez, singleSubWord_b2w, sz, ofNat_add_one]
      refine ⟨pre, ⟨⟨⟨by simp; omega, by simp⟩, b2w_zero_or_one c⟩, by omega⟩⟩
    · rw [mcDivSubAux1_def]
      simp only [ne, if_false, sub, tn, ey, ez, singleSubWord_b2w, sz, ofNat_add_one, eq]
      simp only [mwSub, List.cons_append, List.length_cons]

/-- Flapjack proof of the local HOL lemma `mc_div_sub1_thm`. -/
theorem mcDivSub1_thm {width : Nat} [NeZero width] {ys zs ys2 zs2 : List (BitVec width)}
    {r8 r9 : BitVec width} {l : Nat} :
    zs.length = ys.length ∧ zs.length + 1 < 2 ^ width ∧ ys.length + 1 ≤ l →
    ∃ r8' r9' l2,
      mcDivSub1Pre (l, BitVec.ofNat width ys.length, r8, r9, ys ++ ys2, zs ++ zs2) ∧
      mcDivSub1 (l, BitVec.ofNat width ys.length, r8, r9, ys ++ ys2, zs ++ zs2) =
        (l2, 0, r8', r9', BitVec.ofNat width ys.length, ys ++ ys2,
          (mwSub ys zs true).1 ++ zs2) ∧
      l ≤ l2 + ys.length + 1 := by
  rintro ⟨hz, hw, hl⟩
  obtain ⟨r8', r9', l2, pre, eq, bound⟩ :=
    mcDivSubAux1_thm_gen ys zs [] [] ys2 zs2 true r8 r9 (l - 1)
      ⟨rfl, hz, by simpa using hw, by omega⟩
  have bT : (b2w true : BitVec width) = 1 := by simp [b2w, b2n]
  simp only [List.nil_append, List.length_nil, bT, hz] at pre eq
  have z0 : (BitVec.ofNat width 0 : BitVec width) = 0 := rfl
  rw [z0] at pre eq
  refine ⟨r8', r9', l2, ?_, ?_, by omega⟩
  · rw [mcDivSub1Pre_def, mcDivSubAuxPre_def]
    simp only [ofNat_add_one]
    exact ⟨pre, by omega⟩
  · rw [mcDivSub1_def, mcDivSubAux_def]
    simp only [ofNat_add_one, eq]

/-- Flapjack proof of the local HOL lemma `mc_idiv_mod_header_thm`. -/
theorem mcIdivModHeader_thm {width : Nat} [NeZero width] {xs ys : List (BitVec width)}
    {t : Bool} :
    xs.length < 2 ^ width →
      mcIdivModHeader (BitVec.ofNat width xs.length, mcHeader (t, ys)) =
        mcHeader (decide (xs ≠ [] ∧ t = true), xs) := by
  intro h
  rw [mcIdivModHeader_def]
  by_cases e : xs = []
  · subst e; simp [mcHeader]
  · have ne : BitVec.ofNat width xs.length ≠ 0 := by
      rw [Ne, ofNat_eq_zero h]; exact fun h' => e (List.eq_nil_of_length_eq_zero h')
    simp only [ne, if_false, mcHeader_sign]
    have := shift_add_b2w (decide (xs ≠ [] ∧ t = true)) xs
    cases t
    · simp only [Bool.false_eq_true, not_false_eq_true, if_true] at this ⊢
      rw [← this]; simp [b2w, b2n]
    · simp only [not_true_eq_false, if_false] at this ⊢
      rw [← this]; simp [e, b2w, b2n]

/-- Flapjack proof of the local HOL lemma `mc_header_XOR`. -/
theorem mcHeader_XOR {width : Nat} [NeZero width] {xs ys : List (BitVec width)} :
    ∀ s t : Bool, (mcHeader (s, xs) ^^^ mcHeader (t, ys)) &&& 1 =
      (b2w (decide (s ≠ t)) : BitVec width) := by
  intro s t
  have h1 : (1 : Nat) < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  have one : (1 : BitVec width).toNat = 1 := by simp [Nat.mod_eq_of_lt h1]
  have hs := congrArg BitVec.toNat (mcHeader_AND_1 (s := s) (xs := xs))
  have ht := congrArg BitVec.toNat (mcHeader_AND_1 (s := t) (xs := ys))
  rw [BitVec.toNat_and, one, Nat.and_one_is_mod] at hs ht
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, one, Nat.and_one_is_mod, BitVec.toNat_xor, Nat.xor_mod_two_eq]
  rw [Nat.add_mod, hs, ht]
  cases s <;> cases t <;> simp [b2w, b2n, Nat.mod_eq_of_lt h1]

/-- Flapjack proof of the local HOL lemma `mc_idiv_thm`. -/
theorem mcIdiv_thm {width : Nat} [NeZero width] {s t : Bool} {xs ys zs : List (BitVec width)}
    {r3 : BitVec width} {l : Nat} :
    xs.length + ys.length ≤ zs.length ∧ zs.length < 2 ^ width / 2 ∧ mwOk xs ∧ mwOk ys ∧
    ys ≠ [] ∧ mcDivMax xs ys zs + 2 * zs.length + 2 ≤ l →
    ∃ zs1 l2,
      mcIdivPre (l, r3, mcHeader (s, xs), mcHeader (t, ys), xs, ys, zs) ∧
      mcIdiv (l, r3, mcHeader (s, xs), mcHeader (t, ys), xs, ys, zs) =
        (l2, mcHeader (mwiDivmodAlt r3 (s, xs) (t, ys)), xs, ys,
          (mwiDivmodAlt r3 (s, xs) (t, ys)).2 ++ zs1) ∧
      ((mwiDivmodAlt r3 (s, xs) (t, ys)).2 ++ zs1).length = zs.length ∧
      l ≤ l2 + mcDivMax xs ys zs + 2 * zs.length + 2 := by
  rintro ⟨hz, hzw, okx, oky, ne, hl⟩
  have hP := Nat.two_pow_pos width
  have hx : xs.length < 2 ^ width / 2 := by omega
  have hy : ys.length < 2 ^ width / 2 := by omega
  have hzw' : zs.length < 2 ^ width := by omega
  have nz : mw2n ys ≠ 0 := by
    intro h; exact ne (by rw [← mwOk_mwFix_ID ys oky]; exact (mwFix_NIL ys).mpr h)
  rcases hdiv : mwDiv xs ys with ⟨res, md, c⟩
  obtain ⟨-, -, hc, hmd⟩ := mwDiv_thm xs ys md res c ⟨hdiv, nz⟩
  subst hc
  rw [mwOk_mwFix_ID ys oky] at hmd
  obtain ⟨zs2, l2, preD, eqD, lenD, nzD, fixD, bD⟩ :=
    mcDiv_thm (r3 := r3) (xs := xs) (ys := ys) (zs := zs) (l := l)
      ⟨ne, okx, oky, hz, hzw', hdiv.symm, by omega⟩
  have spec : mwiDivmod (s, xs) (t, ys) =
      (true, ((if (if s = t then mwFix res else if mwFix md = [] then mwFix res
          else mwAddv (mwFix res) [] true) = [] then false else s != t),
          (if s = t then mwFix res else if mwFix md = [] then mwFix res
          else mwAddv (mwFix res) [] true)),
        (if (if s = t then mwFix md else if mwFix md = [] then mwFix md
          else mwSubv ys (mwFix md)) = [] then false else t),
        (if s = t then mwFix md else if mwFix md = [] then mwFix md
          else mwSubv ys (mwFix md))) := by
    simp only [mwiDivmod, hdiv]
  rw [mcIdivPre_def, mcIdiv_def]
  simp only [mc_length hx, mc_length hy, mcHeader_XOR, eqD]
  rw [mcIdiv0Pre_def, mcIdiv0_def]
  have b0 : (b2w false : BitVec width) = 0 := by simp [b2w, b2n]
  have b1 : (b2w true : BitVec width) ≠ 0 := by simp [b2w, b2n, NeZero.ne]
  by_cases h3 : r3 = 0
  · subst h3
    have nz2 : zs2.length ≠ 0 := nzD rfl
    simp only [if_true] at eqD lenD preD
    simp only [if_true]
    simp only [List.length_append] at lenD
    obtain ⟨r8F, lF, preF, eqF, bF⟩ :=
      mcFix_thm res zs2 (BitVec.ofNat width res.length) (l2 - 1) ⟨by omega, by omega⟩
    simp only [eqF]
    have lfr := length_mwFix res
    have hR0 : BitVec.ofNat width (mwFix res).length = 0 ↔ mwFix res = [] := by
      rw [ofNat_eq_zero (by omega)]; exact List.length_eq_zero_iff
    simp only [mwiDivmodAlt, if_true, mwiDiv, spec]
    by_cases hst : s = t
    · subst hst
      simp only [ne_eq, not_true_eq_false, decide_false, b0, if_true, bne_self_eq_false]
      rw [mcAdd1CallPre_def, mcAdd1Call_def]
      simp only [if_true]
      by_cases hr : mwFix res = []
      · simp only [hr.symm ▸ hR0.mpr hr, if_true, hr]
        refine ⟨List.replicate res.length 0 ++ zs2, lF, ⟨preD, ⟨preF, by omega⟩, trivial⟩,
          by simp [mcHeader], by simp; omega, by omega⟩
      · have ne0 : ¬ BitVec.ofNat width (mwFix res).length = 0 := fun h => hr (hR0.mp h)
        simp only [ne0, if_false, hr]
        refine ⟨List.replicate (res.length - (mwFix res).length) 0 ++ zs2, lF,
          ⟨preD, ⟨preF, by omega⟩, trivial⟩, ?_, by simp; omega, by omega⟩
        rw [← b0, shift_add_b2w]; simp
    · have dst : decide (s ≠ t) = true := decide_eq_true hst
      have bst : (s != t) = true := by cases s <;> cases t <;> simp_all
      simp only [hst, if_false, dst, bst]
      rw [mcAdd1CallPre_def, mcAdd1Call_def]
      simp only [b1, if_false]
      have lmd : (mwFix md).length < 2 ^ width := by have := length_mwFix md; omega
      have hM0 : BitVec.ofNat width (mwFix md).length = 0 ↔ mwFix md = [] := by
        rw [ofNat_eq_zero lmd]; exact List.length_eq_zero_iff
      by_cases hm : mwFix md = []
      · simp only [hm, List.length_nil, show (BitVec.ofNat width 0 : BitVec width) = 0 from rfl,
          if_true]
        by_cases hr : mwFix res = []
        · simp only [hr.symm ▸ hR0.mpr hr, if_true, hr]
          refine ⟨List.replicate res.length 0 ++ zs2, lF, ⟨preD, ⟨preF, by omega⟩, trivial⟩,
            by simp [mcHeader], by simp; omega, by omega⟩
        · have ne0 : ¬ BitVec.ofNat width (mwFix res).length = 0 := fun h => hr (hR0.mp h)
          simp only [ne0, if_false, hr]
          refine ⟨List.replicate (res.length - (mwFix res).length) 0 ++ zs2, lF,
            ⟨preD, ⟨preF, by omega⟩, trivial⟩, ?_, by simp; omega, by omega⟩
          rw [shift_add_b2w]; simp
      · have ne0 : ¬ BitVec.ofNat width (mwFix md).length = 0 := fun h => hm (hM0.mp h)
        simp only [ne0, if_false, hm]
        have z2 : List.replicate (res.length - (mwFix res).length) 0 ++ zs2 ≠ [] := by
          intro e; have := congrArg List.length e
          simp only [List.length_append, List.length_replicate, List.length_nil] at this; omega
        obtain ⟨rest, lG, preG, eqG, ltG, lenG, bG⟩ :=
          mcAdd1_thm (zs2 := List.replicate (res.length - (mwFix res).length) 0 ++ zs2)
            (mwFix res) (lF - 1) ⟨by omega, z2, by omega⟩
        have not0 : (BitVec.ofNat width 0 : BitVec width) = 0 := rfl
        have hnt : (~~~(0 : BitVec width)) = ~~~0 := rfl
        simp only [List.append_assoc, eqG]
        have hne : mwAddv (mwFix res) [] true ≠ [] := by
          cases h : mwFix res with
          | nil => simp [mwAddv]
          | cons a b => rw [mwAddv_cons_nil_true]; split <;> simp
        have ne1 : ¬ BitVec.ofNat width (mwAddv (mwFix res) [] true).length = 0 := by
          rw [ofNat_eq_zero ltG]; exact fun h => hne (List.eq_nil_of_length_eq_zero h)
        simp only [ne1, if_false, hne]
        refine ⟨rest, lG, ⟨preD, ⟨preF, by omega⟩, preG, by omega⟩, ?_, ?_, by omega⟩
        · rw [shift_add_b2w]
        · simp only [List.length_append, List.length_replicate] at lenG ⊢; omega
  · simp only [h3, if_false] at eqD lenD preD
    simp only [h3, if_false]
    simp only [List.length_append] at lenD
    simp only [mwiDivmodAlt, h3, if_false, mwiMod, spec]
    rw [mcDivSubCallPre_def, mcDivSubCall_def]
    simp only [mc_length hy]
    have lfm := length_mwFix md
    have hfm := mwFix_thm md
    have lmd : (mwFix md).length < 2 ^ width := by omega
    have sgn : ∀ L : List (BitVec width),
        decide (L ≠ [] ∧ t = true) = (if L = [] then false else t) := by
      intro L; by_cases h : L = [] <;> cases t <;> simp [h]
    by_cases hst : s = t
    · subst hst
      simp only [ne_eq, not_true_eq_false, decide_false, b0, if_true]
      rw [mcIdivModHeader_thm lmd, sgn]
      refine ⟨List.replicate (md.length - (mwFix md).length) 0 ++ zs2, l2, ⟨preD, trivial⟩, ?_,
        by simp; omega, by omega⟩
      rw [← List.append_assoc, hfm]
    · have dst : decide (s ≠ t) = true := decide_eq_true hst
      simp only [hst, if_false, dst, b1]
      have hM0 : BitVec.ofNat width (mwFix md).length = 0 ↔ mwFix md = [] := by
        rw [ofNat_eq_zero lmd]; exact List.length_eq_zero_iff
      by_cases hm : mwFix md = []
      · have hz0 : BitVec.ofNat width (mwFix md).length = 0 := hM0.mpr hm
        simp only [hz0, if_true]
        have := mcIdivModHeader_thm (xs := ([] : List (BitVec width))) (ys := ys) (t := t)
          (by simp)
        simp only [List.length_nil] at this
        rw [show (BitVec.ofNat width 0 : BitVec width) = 0 from rfl] at this
        rw [this, hm]
        refine ⟨md ++ zs2, l2, ⟨preD, trivial⟩, by simp, by simp; omega, by omega⟩
      · have ne0 : ¬ BitVec.ofNat width (mwFix md).length = 0 := fun h => hm (hM0.mp h)
        simp only [ne0, if_false, hm]
        obtain ⟨r8', r9', l3, pre3, eq3, b3⟩ :=
          mcDivSub1_thm (ys := ys) (zs := md) (ys2 := []) (zs2 := zs2)
            (r8 := BitVec.ofNat width (mwFix md).length)
            (r9 := BitVec.ofNat width (mwFix md).length) (l := l2) ⟨by omega, by omega, by omega⟩
        simp only [List.append_nil] at pre3 eq3
        have lS : (mwSub ys md true).1.length = ys.length := by
          rcases h : mwSub ys md true with ⟨S, c⟩
          have := length_mwSub _ _ _ _ _ h; simpa using this.symm
        obtain ⟨r8F, lF, preF, eqF, bF⟩ :=
          mcFix_thm (mwSub ys md true).1 zs2 r8' (l3 - 1) ⟨by omega, by omega⟩
        rw [lS] at preF eqF bF
        simp only [eq3, eqF]
        have hsv : mwFix (mwSub ys md true).1 = mwSubv ys (mwFix md) := by
          rw [mwSubv, mwSub_mwFix]
        have lsv := length_mwFix (mwSub ys md true).1
        rw [hsv] at lsv eqF ⊢
        rw [mcIdivModHeader_thm (by omega), sgn]
        refine ⟨List.replicate (ys.length - (mwSubv ys (mwFix md)).length) 0 ++ zs2, lF,
          ⟨preD, pre3, preF, by omega⟩, by simp, by simp; omega, by omega⟩

end Flapjack.Misc.Multiword
