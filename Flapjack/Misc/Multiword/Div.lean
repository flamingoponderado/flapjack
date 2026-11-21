module

public import Flapjack.Misc.Multiword.DivAux
public import Flapjack.Misc.RichList
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Multiword division with remainder. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Division of digit lists, returning quotient digits, remainder digits and
a flag reporting that the single-word divisions were in range. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwDiv {width : Nat} [NeZero width] (xs ys : List (BitVec width)) :
    List (BitVec width) × List (BitVec width) × Bool :=
  let xs := mwFix xs
  let ys := mwFix ys
  if xs.length < ys.length then
    ([], xs ++ List.replicate (ys.length - xs.length) 0, true)
  else if ys.length = 1 then
    let (qs, r, c) := mwSimpleDiv 0 xs.reverse (holHd ys)
    (qs.reverse, [r], c)
  else
    let d := calcD (holLast ys, 1)
    let xs := mwMulBySingle d xs ++ [0]
    let xs1 := holButlastn ys.length xs
    let xs2 := holLastn ys.length xs
    let ys := (mwMulBySingle d ys).dropLast
    let (qs, rs) := mwDivAux xs1 xs2 ys
    let (rs, _, c) := mwSimpleDiv 0 rs.reverse d
    (qs.reverse, rs.reverse, c)

private theorem rv {width : Nat} [NeZero width] (x : BitVec width) (xs : List (BitVec width)) :
    mw2n (x :: xs).reverse = mw2n xs.reverse + dimwords width xs.length * x.toNat := by
  rw [List.reverse_cons, mw2n_msf, List.length_reverse]

private theorem mw2n_cons' {width : Nat} [NeZero width] (x : BitVec width) (xs : List (BitVec width)) :
    mw2n (x :: xs) = x.toNat + 2 ^ width * mw2n xs := rfl

/-- One step of the main loop chooses the exact quotient digit. -/
private theorem adjust_guess_exact {width : Nat} [NeZero width] (W ys : List (BitVec width))
    (ylen : 2 ≤ ys.length) (wlen : W.length = ys.length + 1)
    (top : 2 ^ width / 2 ≤ (holLast ys).toNat)
    (small : mw2n W < 2 ^ width * mw2n ys) :
    (mwDivAdjust (mwDivGuess W.reverse ys.reverse) W ys).toNat = mw2n W / mw2n ys := by
  -- expose the three leading digits of the window and two of the divisor
  obtain ⟨vs', v2, v1, hys⟩ : ∃ vs' v2 v1, ys = vs' ++ [v2, v1] := by
    obtain ⟨a, v1, h1⟩ := List.eq_nil_or_concat ys |>.resolve_left (by
      intro e; rw [e] at ylen; simp at ylen)
    obtain ⟨b, v2, h2⟩ := List.eq_nil_or_concat a |>.resolve_left (by
      intro e; rw [h1, e] at ylen; simp at ylen)
    exact ⟨b, v2, v1, by rw [h1, h2]; simp⟩
  obtain ⟨us', u3, u2, u1, hW⟩ : ∃ us' u3 u2 u1, W = us' ++ [u3, u2, u1] := by
    have : 3 ≤ W.length := by omega
    obtain ⟨a, u1, h1⟩ := List.eq_nil_or_concat W |>.resolve_left (by
      intro e; rw [e] at this; simp at this)
    obtain ⟨b, u2, h2⟩ := List.eq_nil_or_concat a |>.resolve_left (by
      intro e; rw [h1, e] at this; simp at this)
    obtain ⟨c, u3, h3⟩ := List.eq_nil_or_concat b |>.resolve_left (by
      intro e; rw [h1, h2, e] at this; simp at this)
    exact ⟨c, u3, u2, u1, by rw [h1, h2, h3]; simp⟩
  have lenEq : us'.reverse.length = vs'.reverse.length := by
    rw [hys] at wlen; rw [hW] at wlen; simp at wlen ⊢; omega
  have revW : W.reverse = u1 :: u2 :: u3 :: us'.reverse := by rw [hW]; simp
  have revY : ys.reverse = v1 :: v2 :: vs'.reverse := by rw [hys]; simp
  have Wval : mw2n W = mw2n (u1 :: u2 :: u3 :: us'.reverse).reverse := by
    rw [← revW, List.reverse_reverse]
  have Yval : mw2n ys = mw2n (v1 :: v2 :: vs'.reverse).reverse := by
    rw [← revY, List.reverse_reverse]
  have v1top : 2 ^ width / 2 ≤ v1.toNat := by
    have e : vs' ++ [v2, v1] = (vs' ++ [v2]) ++ [v1] := by simp
    rw [hys, e, holLast_append_singleton] at top
    exact top
  have hb : 2 ≤ 2 ^ width := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (Nat.pos_of_ne_zero (NeZero.ne width))
  have vpos : 0 < v1.toNat := by omega
  have Ypos : 0 < mw2n ys := by
    rw [Yval, rv]
    have : 0 < dimwords width (v2 :: vs'.reverse).length * v1.toNat :=
      Nat.mul_pos (dimwords_pos _) vpos
    omega
  have qsmall : mw2n W / mw2n ys < 2 ^ width := (Nat.div_lt_iff_lt_mul Ypos).mpr (by
    linarith [small])
  have thm := mwDivTest_thm u1 u2 u3 us'.reverse v1 v2 vs'.reverse
    ⟨lenEq, v1top, by rw [← Wval, ← Yval]; exact qsmall⟩
  simp only at thm
  rw [← Wval, ← Yval] at thm
  have guess : mwDivGuess W.reverse ys.reverse =
      mwDivTest (if u1.toNat < v1.toNat then (singleDiv u1 u2 v1).1
        else BitVec.ofNat width (2 ^ width - 1)) u1 u2 u3 v1 v2 := by
    rw [revW, revY]; simp only [mwDivGuess, holHd, List.tail_cons]; rfl
  rw [guess]
  generalize mwDivTest _ u1 u2 u3 v1 v2 = t at thm ⊢
  obtain ⟨_, ht⟩ := thm
  have ⟨mval, mlen⟩ := mwMulBySingle_lemma t ys
  have cmp := mwCmpThm W (mwMulBySingle t ys) (by rw [mlen, wlen])
  rw [mval] at cmp
  simp only [mwDivAdjust]
  rcases ht with ht | ht
  · -- the test digit is exact, so its multiple does not exceed the window
    have le : t.toNat * mw2n ys ≤ mw2n W := by
      rw [ht]; exact Nat.div_mul_le_self _ _
    have notlt : ¬ mw2n W < t.toNat * mw2n ys := by omega
    have hc : mwCmp W (mwMulBySingle t ys) ≠ some true := by
      rw [cmp]
      by_cases e : mw2n W = t.toNat * mw2n ys
      · rw [if_pos e]; simp
      · rw [if_neg e]; simp [notlt]
    rw [if_neg hc, ht]
  · -- one too large: its multiple exceeds the window
    have gt : mw2n W < t.toNat * mw2n ys := by
      rw [ht, Nat.add_mul, Nat.one_mul]
      have := Nat.lt_mul_div_succ (mw2n W) Ypos
      linarith
    have hc : mwCmp W (mwMulBySingle t ys) = some true := by
      rw [cmp, if_neg (Nat.ne_of_lt gt)]; simp [gt]
    rw [if_pos hc, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) t.isLt), ht]
    rfl

/-- Correctness invariant of the main loop on a normalised divisor. -/
private theorem mwDivAux_correct {width : Nat} [NeZero width] (ys : List (BitVec width))
    (ylen : 2 ≤ ys.length) (top : 2 ^ width / 2 ≤ (holLast ys).toNat) :
    ∀ (zs1 zs2 qs rs : List (BitVec width)), zs2.length = ys.length → mw2n zs2 < mw2n ys →
      mwDivAux zs1 zs2 ys = (qs, rs) →
      mw2n qs.reverse * mw2n ys + mw2n rs = mw2n zs1 + dimwords width zs1.length * mw2n zs2 ∧
        mw2n rs < mw2n ys := by
  intro zs1
  induction h : zs1.length using Nat.strong_induction_on generalizing zs1 with
  | _ n ih =>
    intro zs2 qs rs len lt eq
    rw [mwDivAux] at eq
    split at eq
    · rename_i e
      subst e
      simp only [Prod.mk.injEq] at eq
      obtain ⟨rfl, rfl⟩ := eq
      simp only [List.length_nil] at h
      subst h
      simp [mw2n, dimwords, lt]
    · rename_i ne
      obtain ⟨zs1', x, rfl⟩ := List.eq_nil_or_concat zs1 |>.resolve_left ne
      rw [List.concat_eq_append] at eq ⊢
      have hn : n = zs1'.length + 1 := by rw [← h]; simp
      subst hn
      simp only [holLast_append_singleton, List.dropLast_concat] at eq
      have Wsmall : mw2n (x :: zs2) < 2 ^ width * mw2n ys := by
        rw [mw2n_cons']
        have := x.isLt
        have : 2 ^ width * (mw2n zs2 + 1) ≤ 2 ^ width * mw2n ys := Nat.mul_le_mul_left _ lt
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      have exact := adjust_guess_exact (x :: zs2) ys ylen (by simp [len]) top Wsmall
      generalize mwDivAdjust _ (x :: zs2) ys = q at eq exact
      have ⟨mval, mlen⟩ := mwMulBySingle_lemma q ys
      have qle : q.toNat * mw2n ys ≤ mw2n (x :: zs2) := by
        rw [exact]; exact Nat.div_mul_le_self _ _
      have subv := mwSub_thm (x :: zs2) (mwMulBySingle q ys) (by rw [mlen]; simp [len])
        (by rw [mval]; exact qle)
      rw [mval] at subv
      rcases hs : mwSub (x :: zs2) (mwMulBySingle q ys) true with ⟨w, c⟩
      rw [hs] at subv eq
      simp only at subv eq
      have wlen : w.length = ys.length + 1 := by
        have := length_mwSub _ _ _ _ _ hs; simp at this; omega
      have rem : mw2n (x :: zs2) - q.toNat * mw2n ys < mw2n ys := by
        rw [exact]
        have Ypos : 0 < mw2n ys := by omega
        have := Nat.lt_mul_div_succ (mw2n (x :: zs2)) Ypos
        rw [Nat.mul_add, Nat.mul_one] at this
        rw [Nat.mul_comm]; omega
      have Ylt := mw2n_lt ys
      have wfront : mw2n w = mw2n w.dropLast := by
        apply mw2n_msf_NIL w
        refine ⟨by intro e; rw [e] at wlen; simp at wlen, ?_⟩
        rw [List.length_dropLast, wlen, Nat.add_sub_cancel]
        omega
      rcases hr : mwDivAux zs1' w.dropLast ys with ⟨qs1, rs1⟩
      rw [hr] at eq
      simp only [Prod.mk.injEq] at eq
      obtain ⟨rfl, rfl⟩ := eq
      have ⟨val, rlt⟩ := ih zs1'.length (by omega) zs1' rfl w.dropLast qs1 rs1
        (by rw [List.length_dropLast, wlen]; rfl) (by rw [← wfront, subv]; exact rem) hr
      refine ⟨?_, rlt⟩
      have qlen := (length_mwDivAux zs1' w.dropLast ys qs1 rs1
        ⟨hr, by rw [List.length_dropLast, wlen]; rfl⟩).2
      rw [rv, qlen, mw2n_append, dimwords_succ]
      rw [← wfront, subv] at val
      simp only [mw2n, Nat.mul_zero, Nat.add_zero]
      rw [mw2n_cons'] at qle subv val
      have e1 : (mw2n qs1.reverse + dimwords width zs1'.length * q.toNat) * mw2n ys + mw2n rs1 =
          (mw2n qs1.reverse * mw2n ys + mw2n rs1) +
            dimwords width zs1'.length * (q.toNat * mw2n ys) := by ring
      rw [e1, val]
      have e2 : dimwords width zs1'.length * (x.toNat + 2 ^ width * mw2n zs2 - q.toNat * mw2n ys) +
          dimwords width zs1'.length * (q.toNat * mw2n ys) =
          dimwords width zs1'.length * (x.toNat + 2 ^ width * mw2n zs2) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel qle]
      have e3 : dimwords width zs1'.length * (x.toNat + 2 ^ width * mw2n zs2) =
          dimwords width zs1'.length * x.toNat +
            2 ^ width * dimwords width zs1'.length * mw2n zs2 := by ring
      omega

private theorem holLastn_append_singleton {α : Type} (n : Nat) (l : List α) (a : α) :
    holLastn (n + 1) (l ++ [a]) = holLastn n l ++ [a] := by
  simp [holLastn]

private theorem length_holLastn {α : Type} (n : Nat) (l : List α) (h : n ≤ l.length) :
    (holLastn n l).length = n := by
  simp [holLastn]; omega

/-- Multiword division computes the quotient and the remainder of the values. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_thm"
  (words_as_type_indexed_bitvec)]
theorem mwDiv_thm {width : Nat} [NeZero width] :
    ∀ (xs ys mod res : List (BitVec width)) (c : Bool),
      mwDiv xs ys = (res, mod, c) ∧ mw2n ys ≠ 0 →
      mw2n res = mw2n xs / mw2n ys ∧ mw2n mod = mw2n xs % mw2n ys ∧ c = true ∧
        mod.length = (mwFix ys).length := by
  rintro xs ys mod res c ⟨eq, nz⟩
  have Ypos : 0 < mw2n ys := Nat.pos_of_ne_zero nz
  simp only [mwDiv] at eq
  have okX : mwOk (mwFix xs) := mwOk_fix xs
  have okY : mwOk (mwFix ys) := mwOk_fix ys
  rw [← mw2n_mwFix xs, ← mw2n_mwFix ys]
  replace Ypos : 0 < mw2n (mwFix ys) := by rw [mw2n_mwFix]; exact Ypos
  clear nz
  generalize mwFix xs = X at eq okX ⊢
  generalize mwFix ys = Y at eq okY Ypos ⊢
  have hb : 2 ≤ 2 ^ width := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (Nat.pos_of_ne_zero (NeZero.ne width))
  split at eq
  · -- the dividend has fewer digits than the divisor
    rename_i short
    simp only [Prod.mk.injEq] at eq
    obtain ⟨rfl, rfl, rfl⟩ := eq
    have lt := length_less_imp_mw2n_less X Y ⟨okX, okY, short⟩
    have gen : ∀ (k : Nat) (z : BitVec width), z.toNat = 0 → mw2n (List.replicate k z) = 0 := by
      intro k z hz
      induction k with
      | zero => rfl
      | succ k ih => simp only [List.replicate_succ, mw2n, hz, ih, Nat.mul_zero]
    have rep : mw2n (X ++ List.replicate (Y.length - X.length) (0 : BitVec width)) = mw2n X := by
      rw [mw2n_append, gen _ _ (by simp), Nat.mul_zero, Nat.add_zero]
    refine ⟨?_, ?_, rfl, ?_⟩
    · simp [mw2n, Nat.div_eq_of_lt lt]
    · rw [rep, Nat.mod_eq_of_lt lt]
    · simp; omega
  · rename_i notShort
    split at eq
    · -- a single-digit divisor
      rename_i one
      obtain ⟨h, rfl⟩ : ∃ h, Y = [h] := by
        match Y, one with
        | [h], _ => exact ⟨h, rfl⟩
      rcases hs : mwSimpleDiv 0 X.reverse (holHd [h]) with ⟨qs, r, c'⟩
      rw [hs] at eq
      simp only [Prod.mk.injEq] at eq
      obtain ⟨rfl, rfl, rfl⟩ := eq
      simp only [holHd] at hs
      have hpos : (0 : BitVec width) < h := by
        rw [BitVec.lt_def]
        have z : (0 : BitVec width).toNat = 0 := by simp
        rw [z]; simpa [mw2n] using Ypos
      obtain ⟨qv, rv', ct⟩ := mwSimpleDiv_thm X.reverse h qs r c' ⟨hs, hpos⟩
      rw [List.reverse_reverse] at qv rv'
      refine ⟨by simpa [mw2n] using qv, by simpa [mw2n] using rv', ct, rfl⟩
    · -- the normalised long division
      rename_i one
      have Yne : Y ≠ [] := by intro e; rw [e] at Ypos; simp [mw2n] at Ypos
      have ylen : 2 ≤ Y.length := by
        have : Y.length ≠ 0 := fun e => Yne (List.eq_nil_of_length_eq_zero e)
        omega
      obtain ⟨vs', v1, hYc⟩ := List.eq_nil_or_concat Y |>.resolve_left Yne
      rw [List.concat_eq_append] at hYc
      subst hYc
      have v1ne : v1 ≠ 0 := (mwOk_snoc vs' v1).mp okY
      have clauses := d_clauses vs'.reverse v1 (NOT_0w_bis v1ne)
      rw [List.reverse_cons, List.reverse_reverse] at clauses
      obtain ⟨dpos, yfront, ytop⟩ := clauses
      simp only [holLast_append_singleton] at eq
      generalize hd : calcD (v1, (1 : BitVec width)) = d at eq dpos yfront ytop
      generalize hYd : (mwMulBySingle d (vs' ++ [v1])).dropLast = Yd at eq yfront ytop
      have ⟨myv, myl⟩ := mwMulBySingle_lemma d (vs' ++ [v1])
      have ydlen : Yd.length = (vs' ++ [v1]).length := by
        rw [← hYd, List.length_dropLast, myl]; rfl
      have ydval : mw2n Yd = d.toNat * mw2n (vs' ++ [v1]) := by
        rw [← yfront, myv]
      have ⟨mxv, mxl⟩ := mwMulBySingle_lemma d X
      generalize hM : mwMulBySingle d X = M at eq mxv mxl
      have xlen : (vs' ++ [v1]).length ≤ (M ++ [(0 : BitVec width)]).length := by
        have ns := notShort
        simp only [List.length_append, List.length_singleton, mxl] at ns ⊢
        omega
      -- the initial window is the zero-topped high part, below the divisor
      have win : mw2n (holLastn (vs' ++ [v1]).length (M ++ [(0 : BitVec width)])) < mw2n Yd := by
        have hl : (vs' ++ [v1]).length = vs'.length + 1 := by simp
        rw [hl, holLastn_append_singleton, mw2n_msf]
        have lenL := length_holLastn vs'.length M (by simp at xlen; omega)
        rw [lenL]
        have := mw2n_lt (holLastn vs'.length M)
        rw [lenL] at this
        rw [show (0 : BitVec width).toNat = 0 by simp, Nat.mul_zero, Nat.add_zero]
        -- the normalised divisor is at least `dimwords (LENGTH vs')`
        obtain ⟨F, t, hF⟩ := List.eq_nil_or_concat Yd |>.resolve_left (by
          intro e; rw [e] at ydlen; simp at ydlen)
        rw [List.concat_eq_append] at hF
        rw [hF, holLast_append_singleton] at ytop
        have Flen : F.length = vs'.length := by
          have := congrArg List.length hF; rw [ydlen] at this; simp at this; omega
        rw [hF, mw2n_msf, Flen]
        have tpos : 1 ≤ t.toNat := by
          have : 1 ≤ 2 ^ width / 2 := by omega
          omega
        have : dimwords width vs'.length ≤ dimwords width vs'.length * t.toNat :=
          Nat.le_mul_of_pos_right _ tpos
        omega
      have split := holButlastn_append_holLastn (vs' ++ [v1]).length (M ++ [(0 : BitVec width)])
      have topY : 2 ^ width / 2 ≤ (holLast Yd).toNat := ytop
      generalize hA : holButlastn (vs' ++ [v1]).length (M ++ [(0 : BitVec width)]) = A at eq split
      generalize hB : holLastn (vs' ++ [v1]).length (M ++ [(0 : BitVec width)]) = B at eq split win
      have Blen : B.length = Yd.length := by
        rw [← hB, ydlen]; exact length_holLastn _ _ xlen
      rcases ha : mwDivAux A B Yd with ⟨qs, rs⟩
      rw [ha] at eq
      have ⟨aux, rlt⟩ := mwDivAux_correct Yd (by rw [ydlen]; exact ylen) topY A B qs rs Blen win ha
      have rslen := (length_mwDivAux A B Yd qs rs ⟨ha, Blen⟩).1
      rcases hsd : mwSimpleDiv 0 rs.reverse d with ⟨rs2, r, c2⟩
      rw [hsd] at eq
      simp only [Prod.mk.injEq] at eq
      obtain ⟨rfl, rfl, rfl⟩ := eq
      have dpos' : (0 : BitVec width) < d := by rw [BitVec.lt_def]; simpa using dpos
      obtain ⟨rv2, _, ct⟩ := mwSimpleDiv_thm rs.reverse d rs2 r c2 ⟨hsd, dpos'⟩
      rw [List.reverse_reverse] at rv2
      -- the value of the normalised dividend
      have total : mw2n A + dimwords width A.length * mw2n B = d.toNat * mw2n X := by
        rw [← mw2n_append, split, mw2n_append, mxv]
        simp [mw2n]
      rw [total, ydval] at aux
      rw [ydval] at rlt
      generalize mw2n (vs' ++ [v1]) = Yv at aux rlt Ypos ⊢
      generalize mw2n X = Xv at aux rlt ⊢
      have dp : 0 < d.toNat := dpos
      have Q : mw2n qs.reverse = Xv / Yv ∧ mw2n rs = d.toNat * (Xv % Yv) := by
        have key : (mw2n qs.reverse) * (d.toNat * Yv) + mw2n rs = d.toNat * Xv := aux
        have hq : d.toNat * Xv / (d.toNat * Yv) = mw2n qs.reverse := by
          rw [← key, Nat.mul_comm (mw2n qs.reverse), Nat.mul_add_div (Nat.mul_pos dp Ypos),
            Nat.div_eq_of_lt rlt, Nat.add_zero]
        rw [Nat.mul_div_mul_left _ _ dp] at hq
        refine ⟨hq.symm, ?_⟩
        have := Nat.mod_add_div (d.toNat * Xv) (d.toNat * Yv)
        rw [Nat.mul_div_mul_left _ _ dp, Nat.mul_mod_mul_left] at this
        rw [← hq] at key
        have e : d.toNat * Yv * (Xv / Yv) = Xv / Yv * (d.toNat * Yv) := Nat.mul_comm _ _
        omega
      refine ⟨Q.1, ?_, ct, ?_⟩
      · rw [rv2, Q.2, Nat.mul_div_cancel_left _ dp]
      · rw [List.length_reverse, ← length_mwSimpleDiv _ _ _ _ _ _ hsd, List.length_reverse,
          rslen, ydlen]

end Flapjack.Misc.Multiword
