module

public import Flapjack.Misc.Multiword.Mc.Correct.DivParts
public import Flapjack.Misc.Multiword.Div

@[expose] public section

/-! Correctness of the machine-code-style unsigned division of HOL's
`mc_multiword` (the local HOL lemma `mc_div_thm`). -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Flapjack proof of the local HOL lemma `mw_fix_REPLICATE`. -/
theorem mwFix_replicate {width : Nat} [NeZero width] (xs : List (BitVec width)) :
    ∀ n : Nat, mwFix (xs ++ List.replicate n 0) = mwFix xs := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [replicate_SNOC, ← List.append_assoc, mwFix_SNOC, ih]

/-- Flapjack proof of the local HOL lemma `MAP_K_0`. -/
theorem map_zero_eq_replicate {width : Nat} (xs : List (BitVec width)) :
    xs.map (fun _ => (0 : BitVec width)) = List.replicate xs.length 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.length_cons, List.replicate_succ, ih]

/-- The case of `mc_div_thm` with a shorter dividend (Flapjack proof). -/
theorem mcDiv_thm_short {width : Nat} [NeZero width] {xs ys zs res md : List (BitVec width)}
    {r3 : BitVec width} {l : Nat}
    (ne : ys ≠ []) (okx : mwOk xs) (oky : mwOk ys) (hz : xs.length + ys.length ≤ zs.length)
    (hzw : zs.length < 2 ^ width) (hdiv : (res, md, true) = mwDiv xs ys)
    (hl : mcDivMax xs ys zs ≤ l) (hlt : xs.length < ys.length) :
    ∃ zs2 l2,
      mcDivPre (l, BitVec.ofNat width xs.length, BitVec.ofNat width ys.length, r3, xs, ys, zs) ∧
      mcDiv (l, BitVec.ofNat width xs.length, BitVec.ofNat width ys.length, r3, xs, ys, zs) =
        (l2, BitVec.ofNat width (if r3 = 0 then res else md).length, r3,
          BitVec.ofNat width (mwFix md).length, xs, ys, (if r3 = 0 then res else md) ++ zs2) ∧
      zs.length = ((if r3 = 0 then res else md) ++ zs2).length ∧
      (r3 = 0 → zs2.length ≠ 0) ∧ (mwFix md).length < 2 ^ width ∧
      l ≤ l2 + mcDivMax xs ys zs := by
  rw [mwDiv] at hdiv
  simp only [mwOk_mwFix_ID xs okx, mwOk_mwFix_ID ys oky, hlt, if_true, Prod.mk.injEq] at hdiv
  obtain ⟨rfl, rfl, -⟩ := hdiv
  have hy : 0 < ys.length := List.length_pos_iff.mpr ne
  have lt : BitVec.ofNat width xs.length < BitVec.ofNat width ys.length := by
    rw [ofNat_lt_ofNat (by omega) (by omega)]; exact hlt
  have fixmd : mwFix (xs ++ List.replicate (ys.length - xs.length) 0) = xs := by
    rw [mwFix_replicate, mwOk_mwFix_ID xs okx]
  simp only [mcDivMax] at hl
  rw [mcDivPre_def, mcDiv_def]
  simp only [lt, if_true, fixmd]
  by_cases h3 : r3 = 0
  · subst h3
    refine ⟨zs, l, ?_, ?_, by simp, fun _ => by omega, by omega, by omega⟩
    · rw [mcDiv0Pre_def]; simp
    · rw [mcDiv0_def]; simp
  · obtain ⟨zs1, zs2, rfl, h1⟩ := less_eq_length zs ys.length (by omega)
    obtain ⟨zs3, zs4, rfl, h3l⟩ := less_eq_length zs1 xs.length (by omega)
    simp only [List.length_append] at hz hzw h1 hl
    obtain ⟨pz, ez⟩ := mcMulZero_thm (zs3 ++ zs4) zs2 (l - 1) ⟨by simp; omega, by simp; omega⟩
    simp only [List.length_append, h1] at pz ez
    obtain ⟨lc, pc, ec, bc⟩ := mcCopyOver_thm xs (zs3.map fun _ => 0) []
      ((zs4.map fun _ => 0) ++ zs2) (l - 1 - ys.length - 1)
      ⟨by simp; omega, by simp; omega, by omega⟩
    simp only [List.append_nil, List.map_append, List.append_assoc] at pc ec ez pz
    refine ⟨zs2, lc, ?_, ?_, ?_, fun h => absurd h h3, by omega,
      by simp only [mcDivMax, List.length_append]; omega⟩
    · rw [mcDiv0Pre_def]
      simp only [h3, if_false, List.append_assoc, ez]
      exact ⟨⟨pz, by omega⟩, pc, by omega⟩
    · rw [mcDiv0_def]
      simp only [h3, if_false, List.append_assoc, ez, ec, List.length_append,
        List.length_replicate]
      rw [map_zero_eq_replicate]
      simp only [Prod.mk.injEq, true_and, List.append_cancel_left_eq]
      constructor
      · congr 1; omega
      · congr 2; omega
    · simp only [h3, if_false, List.length_append, List.length_replicate]; omega

/-- The case of `mc_div_thm` with a single-digit divisor (Flapjack proof). -/
theorem mcDiv_thm_single {width : Nat} [NeZero width] {xs ys zs res md : List (BitVec width)}
    {r3 : BitVec width} {l : Nat}
    (okx : mwOk xs) (oky : mwOk ys) (hz : xs.length + ys.length ≤ zs.length)
    (hzw : zs.length < 2 ^ width) (hdiv : (res, md, true) = mwDiv xs ys)
    (hl : mcDivMax xs ys zs ≤ l) (hlt : ¬ xs.length < ys.length) (h1 : ys.length = 1) :
    ∃ zs2 l2,
      mcDivPre (l, BitVec.ofNat width xs.length, BitVec.ofNat width ys.length, r3, xs, ys, zs) ∧
      mcDiv (l, BitVec.ofNat width xs.length, BitVec.ofNat width ys.length, r3, xs, ys, zs) =
        (l2, BitVec.ofNat width (if r3 = 0 then res else md).length, r3,
          BitVec.ofNat width (mwFix md).length, xs, ys, (if r3 = 0 then res else md) ++ zs2) ∧
      zs.length = ((if r3 = 0 then res else md) ++ zs2).length ∧
      (r3 = 0 → zs2.length ≠ 0) ∧ (mwFix md).length < 2 ^ width ∧
      l ≤ l2 + mcDivMax xs ys zs := by
  obtain ⟨y, rfl⟩ : ∃ y, ys = [y] := by
    match ys, h1 with
    | [y], _ => exact ⟨y, rfl⟩
  have hlt1 : ¬ xs.length < 1 := by simpa using hlt
  rw [mwDiv] at hdiv
  simp only [mwOk_mwFix_ID xs okx, mwOk_mwFix_ID [y] oky, List.length_singleton, hlt1, if_false,
    if_true, holHd] at hdiv
  rcases hs : mwSimpleDiv 0 xs.reverse y with ⟨qs, r, c⟩
  simp only [hs, Prod.mk.injEq] at hdiv
  obtain ⟨rfl, rfl, rfl⟩ := hdiv
  simp only [List.length_singleton] at hz hlt hl
  have lq := length_mwSimpleDiv _ _ _ _ _ _ hs
  simp only [List.length_reverse] at lq
  have nlt : ¬ BitVec.ofNat width xs.length < BitVec.ofNat width [y].length := by
    rw [ofNat_lt_ofNat (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) hz) hzw)
      (by simpa using Nat.one_lt_two_pow (NeZero.ne width))]; simpa using hlt
  have hone : BitVec.ofNat width [y].length = (1 : BitVec width) := rfl
  have nlt1 : ¬ BitVec.ofNat width xs.length < (1 : BitVec width) := by rw [← hone]; exact nlt
  obtain ⟨zs1, zs2, rfl, hz1⟩ := less_eq_length zs xs.length (by omega)
  simp only [List.length_append] at hz hzw hl
  simp only [mcDivMax, List.length_append, List.length_singleton] at hl
  obtain ⟨pre, eq⟩ := mcSimpleDiv_thm xs [] zs1 zs2 0 y qs r (l - 1)
    ⟨by omega, hz1, by omega, hs⟩
  simp only [List.append_nil] at pre eq
  have t0 : (0 : BitVec width).toNat = 0 := by simp
  have hfix : (mwFix [r]).length = if r = 0 then 0 else 1 := by
    rw [show [r] = [] ++ [r] from rfl, mwFix_snoc]
    split
    · simp [mwFix]
    · simp
  rw [mcDivPre_def, mcDiv_def]
  simp only [hone, nlt1, if_false, if_true]
  rw [mcDiv1Pre_def, mcDiv1_def]
  simp only [t0, holEl, holHd, eq, hfix]
  have hb : ((if r = 0 then 0 else 1 : Nat)) < 2 ^ width := by
    have := Nat.one_lt_two_pow (NeZero.ne width); split <;> omega
  have bnd : l ≤ l - 1 - xs.length + mcDivMax xs [y] (zs1 ++ zs2) := by
    simp only [mcDivMax, List.length_append, List.length_singleton]; omega
  by_cases h3 : r3 = 0
  · subst h3
    refine ⟨zs2, l - 1 - xs.length, ?_, ?_, ?_, fun _ => by omega, hb, bnd⟩
    · simp only [if_true]; split <;> exact ⟨by simp, pre, by omega⟩
    · simp only [if_true, List.length_reverse, ← lq]
      split <;> simp
    · simp [← lq, hz1]
  · obtain ⟨q, qt, hq⟩ : ∃ q qt, qs.reverse = q :: qt := by
      cases e : qs.reverse with
      | nil =>
        have : qs.reverse.length = 0 := by rw [e]; rfl
        simp only [List.length_reverse] at this; omega
      | cons a b => exact ⟨a, b, rfl⟩
    have hqt : qt.length + 1 = xs.length := by
      have := congrArg List.length hq; simp at this; omega
    refine ⟨qt ++ zs2, l - 1 - xs.length, ?_, ?_, ?_, fun h => absurd h h3, hb, bnd⟩
    · simp only [h3, if_false]
      split <;> exact ⟨⟨by simp, pre, by omega⟩, by simp; omega⟩
    · simp only [h3, if_false, hq]
      split <;> simp
    · simp only [h3, if_false, List.length_append, List.length_singleton]; omega

/-- `BUTLASTN` of a known split (Flapjack helper). -/
theorem holButlastn_append {α : Type} (a b : List α) :
    holButlastn b.length (a ++ b) = a := by
  simp [holButlastn]

/-- `LASTN` of a known split (Flapjack helper). -/
theorem holLastn_append {α : Type} (a b : List α) :
    holLastn b.length (a ++ b) = b := by
  simp [holLastn]

/-- `EL` of the last index is `LAST` (Flapjack helper). -/
theorem holEl_pred_length {α : Type} [Nonempty α] (ys : List α) (h : ys ≠ []) :
    holEl (ys.length - 1) ys = holLast ys := by
  obtain ⟨ys', y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left h
  simp only [List.concat_eq_append, List.length_append, List.length_singleton,
    Nat.add_sub_cancel, holLast_append_singleton]
  simpa using holEl_append_length ys' [] y

/-- The general case of `mc_div_thm`, with a divisor of at least two digits
(Flapjack proof). -/
theorem mcDiv_thm_long {width : Nat} [NeZero width] {xs ys zs res md : List (BitVec width)}
    {r3 : BitVec width} {l : Nat}
    (ne : ys ≠ []) (okx : mwOk xs) (oky : mwOk ys) (hz : xs.length + ys.length ≤ zs.length)
    (hzw : zs.length < 2 ^ width) (hdiv : (res, md, true) = mwDiv xs ys)
    (hl : mcDivMax xs ys zs ≤ l) (hlt : ¬ xs.length < ys.length) (h1 : ¬ ys.length = 1) :
    ∃ zs2 l2,
      mcDivPre (l, BitVec.ofNat width xs.length, BitVec.ofNat width ys.length, r3, xs, ys, zs) ∧
      mcDiv (l, BitVec.ofNat width xs.length, BitVec.ofNat width ys.length, r3, xs, ys, zs) =
        (l2, BitVec.ofNat width (if r3 = 0 then res else md).length, r3,
          BitVec.ofNat width (mwFix md).length, xs, ys, (if r3 = 0 then res else md) ++ zs2) ∧
      zs.length = ((if r3 = 0 then res else md) ++ zs2).length ∧
      (r3 = 0 → zs2.length ≠ 0) ∧ (mwFix md).length < 2 ^ width ∧
      l ≤ l2 + mcDivMax xs ys zs := by
  have hP := Nat.two_pow_pos width
  have hy2 : 2 ≤ ys.length := by
    have := List.length_pos_iff.mpr ne; omega
  -- the specification
  rw [mwDiv] at hdiv
  simp only [mwOk_mwFix_ID xs okx, mwOk_mwFix_ID ys oky, hlt, h1, if_false] at hdiv
  generalize hd : calcD (holLast ys, 1) = d at hdiv
  have lM : (mwMulBySingle d xs ++ [0]).length = xs.length + 2 := by
    simp [length_mwMulBySingle]
  obtain ⟨ts1, ts2, hX, hts2⟩ :=
    less_eq_length_alt (mwMulBySingle d xs ++ [0]) ys.length (by omega)
  have hts1 : ts1.length + ys.length = xs.length + 2 := by
    have := congrArg List.length hX; rw [lM, List.length_append] at this; omega
  rw [hX, ← hts2, holButlastn_append, holLastn_append] at hdiv
  rcases hqr : mwDivAux ts1 ts2 (mwMulBySingle d ys).dropLast with ⟨qs, rs⟩
  rcases hsd : mwSimpleDiv 0 rs.reverse d with ⟨x1, x2, c⟩
  simp only [hqr, hsd, Prod.mk.injEq] at hdiv
  obtain ⟨rfl, rfl, rfl⟩ := hdiv
  have hYlen : (mwMulBySingle d ys).dropLast.length = ys.length := by
    rw [List.length_dropLast, length_mwMulBySingle]; omega
  obtain ⟨lrs, lqs⟩ := length_mwDivAux ts1 ts2 _ qs rs ⟨hqr, by omega⟩
  have lx1 := length_mwSimpleDiv _ _ _ _ _ _ hsd
  simp only [List.length_reverse] at lx1
  -- the machine-code side
  simp only [mcDivMax] at hl
  have K0 : ts1.length * (2 ^ width + 2 * ys.length + 4) ≤
      xs.length * (2 ^ width + 2 * ys.length + 4) := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨zs1, zrest, rfl, hz1⟩ := less_eq_length zs xs.length (by omega)
  obtain ⟨z1, z2, zs2, rfl⟩ : ∃ z1 z2 zs2, zrest = z1 :: z2 :: zs2 := by
    have : 2 ≤ zrest.length := by simp only [List.length_append] at hz; omega
    match zrest, this with
    | a :: b :: c, _ => exact ⟨a, b, c, rfl⟩
  simp only [List.length_append, List.length_cons] at hz hzw hl
  have hlast : holLast ys ≠ 0 := oky ne
  obtain ⟨lA, preA, eqA, bA⟩ :=
    mcCalcD_thm (v1 := holLast ys) (d := 1) (l := l - 1) ⟨hlast, by omega⟩
  rw [hd] at eqA
  obtain ⟨r1B, lB, preB, eqB, bB⟩ :=
    mcMulBySingle_thm xs d zs1 (z2 :: zs2) z1 (lA - 1) ⟨by omega, hz1, by omega, by omega⟩
  have hset : (mwMulBySingle d xs ++ z2 :: zs2).set (zs1.length + 1) 0 = ts1 ++ ts2 ++ zs2 := by
    rw [← hX]
    rw [show zs1.length + 1 = (mwMulBySingle d xs).length by rw [length_mwMulBySingle]; omega]
    simp
  have tB : (BitVec.ofNat width (zs1.length + 1)).toNat = zs1.length + 1 :=
    ofNat_toNat_of_lt (by omega)
  obtain ⟨lC, preC, eqC, bC⟩ :=
    mcTopTwo_thm (ys := ys) (x := d) (l := lB - 1) ⟨by omega, by omega, by omega⟩
  have e10 : BitVec.ofNat width xs.length - BitVec.ofNat width ys.length + 2 =
      BitVec.ofNat width ts1.length := by
    rw [ofNat_sub_ofNat (by omega) (by omega),
      show (2 : BitVec width) = BitVec.ofNat width 2 from rfl, ofNat_add_ofNat]
    congr 1; omega
  have hv : holLast (mwMulBySingle d ys).dropLast ≠ 0 := by
    rw [← hd]; exact last_front_mwMulBySingle_NOT_ZERO ⟨oky, ne, by omega⟩
  obtain ⟨lD, preD, eqD, bD⟩ :=
    mcDivLoop_thm (d := d) (ys := ys) ts1 ts2 zs2 (lC - 1)
      ⟨by omega, by simp only [List.length_append]; omega, by omega, hv, by omega⟩
  rw [hqr] at eqD
  simp only at eqD
  obtain ⟨preE, eqE⟩ := mcSimpleDiv1_thm rs (qs.reverse ++ zs2) 0 d x1 x2 (lD - 1)
    ⟨by omega, by omega, hsd⟩
  have hfx := mwFix_thm x1.reverse
  have lfx := length_mwFix x1.reverse
  simp only [List.length_reverse] at lfx hfx
  obtain ⟨r8F, lF, preF, eqF, bF⟩ := mcFix_thm x1.reverse (qs.reverse ++ zs2)
    (BitVec.ofNat width ts1.length) (lD - 1 - rs.length - 1) ⟨by simp; omega, by simp; omega⟩
  simp only [List.length_reverse] at eqF preF
  rw [hfx] at eqF
  have hrs : rs.length = ys.length := by omega
  have hx1 : x1.length = ys.length := by omega
  rw [hrs] at eqE preE
  rw [hx1] at eqF preF
  rw [hrs] at eqF preF bF
  simp only [List.append_assoc] at eqD preD eqF preF
  have nlt : ¬ BitVec.ofNat width xs.length < BitVec.ofNat width ys.length := by
    rw [ofNat_lt_ofNat (by omega) (by omega)]; exact hlt
  have hne1 : BitVec.ofNat width ys.length ≠ 1 := by
    rw [show (1 : BitVec width) = BitVec.ofNat width 1 from rfl, Ne, ofNat_inj (by omega) (by omega)]
    exact h1
  have s1 : BitVec.ofNat width ys.length - 1 = BitVec.ofNat width (ys.length - 1) :=
    ofNat_sub_one (by omega) (by omega)
  have t1 : (BitVec.ofNat width (ys.length - 1)).toNat = ys.length - 1 :=
    ofNat_toNat_of_lt (by omega)
  have el : holEl (ys.length - 1) ys = holLast ys := holEl_pred_length ys ne
  rw [mcDivPre_def, mcDiv_def]
  simp only [nlt, if_false, hne1, s1, t1, el, eqA]
  rw [mcDiv3Pre_def, mcDiv3_def]
  simp only [eqB, tB, hset, eqC, e10, List.append_assoc, eqD]
  rw [mcDiv2Pre_def, mcDiv2_def]
  simp only [eqE, eqF]
  simp only [List.length_reverse, hx1] at bF
  have lmb : zs1.length + 1 < (mwMulBySingle d xs ++ z2 :: zs2).length := by
    simp [length_mwMulBySingle]; omega
  have lq1 : qs.reverse.length = ts1.length := by simp [lqs]
  have g0 : ys.length - 1 < ys.length := by omega
  have g1 : l ≠ 0 := by omega
  have g2 : lA ≠ 0 := by omega
  have g3 : lB ≠ 0 := by omega
  have g4 : lC ≠ 0 := by omega
  have g5 : lD ≠ 0 := by omega
  have g6 : lD - 1 - ys.length ≠ 0 := by omega
  have g7 : ts1.length ≤ lF - 1 := by omega
  have g8 : lF ≠ 0 := by omega
  by_cases h3 : r3 = 0
  · subst h3
    obtain ⟨zs4, lG, preG, eqG, lenG, bG⟩ :=
      mcCopyDown_thm x1.reverse qs.reverse zs2 (lF - 1) ⟨by simp; omega, by
        intro e; have := congrArg List.length e
        simp only [List.length_reverse, List.length_nil] at this; omega, by rw [lq1]; exact g7⟩
    simp only [List.length_reverse, hx1, lqs, List.append_assoc] at preG eqG lenG bG
    simp only [if_true, eqG]
    refine ⟨zs4, lG, ⟨⟨g0, preA, g1⟩, ⟨⟨⟨⟨preB, g2⟩, lmb⟩, preC, g3⟩,
      preD, g4⟩, ⟨⟨preE, g5⟩, preF, g6⟩, preG, g8⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp [lqs]
    · simp only [List.length_append, List.length_reverse, List.length_cons, lqs]; omega
    · intro _; omega
    · omega
    · simp only [mcDivMax, List.length_append, List.length_cons]; omega
  · simp only [h3, if_false]
    refine ⟨qs.reverse ++ zs2, lF, ⟨⟨g0, preA, g1⟩, ⟨⟨⟨⟨preB, g2⟩, lmb⟩, preC,
      g3⟩, preD, g4⟩, ⟨preE, g5⟩, preF, g6⟩, ?_, ?_, fun h => h.elim, ?_, ?_⟩
    · simp [hx1]
    · simp only [List.length_append, List.length_reverse, List.length_cons, lqs, hx1]; omega
    · omega
    · simp only [mcDivMax, List.length_append, List.length_cons]; omega

/-- Flapjack proof of the local HOL lemma `mc_div_thm`. -/
theorem mcDiv_thm {width : Nat} [NeZero width] {xs ys zs res md : List (BitVec width)}
    {r3 : BitVec width} {l : Nat} :
    ys ≠ [] ∧ mwOk xs ∧ mwOk ys ∧ xs.length + ys.length ≤ zs.length ∧
    zs.length < 2 ^ width ∧ (res, md, true) = mwDiv xs ys ∧ mcDivMax xs ys zs ≤ l →
    ∃ zs2 l2,
      mcDivPre (l, BitVec.ofNat width xs.length, BitVec.ofNat width ys.length, r3, xs, ys, zs) ∧
      mcDiv (l, BitVec.ofNat width xs.length, BitVec.ofNat width ys.length, r3, xs, ys, zs) =
        (l2, BitVec.ofNat width (if r3 = 0 then res else md).length, r3,
          BitVec.ofNat width (mwFix md).length, xs, ys, (if r3 = 0 then res else md) ++ zs2) ∧
      zs.length = ((if r3 = 0 then res else md) ++ zs2).length ∧
      (r3 = 0 → zs2.length ≠ 0) ∧ (mwFix md).length < 2 ^ width ∧
      l ≤ l2 + mcDivMax xs ys zs := by
  rintro ⟨ne, okx, oky, hz, hzw, hdiv, hl⟩
  by_cases hlt : xs.length < ys.length
  · exact mcDiv_thm_short ne okx oky hz hzw hdiv hl hlt
  by_cases h1 : ys.length = 1
  · exact mcDiv_thm_single okx oky hz hzw hdiv hl hlt h1
  · exact mcDiv_thm_long ne okx oky hz hzw hdiv hl hlt h1

end Flapjack.Misc.Multiword
