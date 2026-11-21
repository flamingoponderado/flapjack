module

public import Flapjack.Misc.Multiword.Mc.Correct.Sub

@[expose] public section

/-! Correctness of the machine-code-style signed addition of HOL's
`mc_multiword`. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Flapjack proof of the local HOL lemma `mc_header_EQ`. -/
theorem mcHeader_EQ {width : Nat} [NeZero width] {s t : Bool} {xs ys : List (BitVec width)} :
    (mcHeader (s, xs) &&& 1 = mcHeader (t, ys) &&& 1) ↔ s = t := by
  rw [mcHeader_AND_1, mcHeader_AND_1]
  cases s <;> cases t <;> simp [b2w, b2n, NeZero.ne]

/-- Flapjack proof of the local HOL lemma `b2w_NOT`. -/
theorem b2w_NOT {width : Nat} [NeZero width] (s : Bool) :
    (b2w s : BitVec width) ^^^ 1 = b2w (!s) := by
  have h1 : (1 : Nat) < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  apply BitVec.eq_of_toNat_eq
  cases s <;> simp [b2w, b2n, Nat.mod_eq_of_lt h1]

/-- A header rebuilt from a length word and a sign word (Flapjack helper). -/
theorem shift_add_b2w {width : Nat} [NeZero width] (s : Bool) (xs : List (BitVec width)) :
    BitVec.ofNat width xs.length <<< 1 + b2w s = mcHeader (s, xs) := by
  have h1 : (1 : Nat) < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  have sh : BitVec.ofNat width xs.length <<< 1 = BitVec.ofNat width (xs.length * 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, pow_one]
    rw [Nat.mod_mul_mod]
  rw [sh, mcHeader]
  cases s <;> simp [b2w, b2n]

/-- Lengths below half the word range fit with room to spare (Flapjack helper). -/
theorem lt_half_succ {width n : Nat} [NeZero width] (h : n < 2 ^ width / 2) :
    n + 1 < 2 ^ width := by
  have := Nat.one_lt_two_pow (NeZero.ne width)
  omega

/-- Flapjack proof of the local HOL lemma `mc_iadd_thm`. -/
theorem mcIadd_thm {width : Nat} [NeZero width] {s t : Bool} {xs ys zs : List (BitVec width)}
    {l : Nat} :
    xs.length < 2 ^ width / 2 ∧ ys.length < 2 ^ width / 2 ∧
    xs.length + ys.length ≤ zs.length ∧ mwOk xs ∧ mwOk ys ∧
    4 * xs.length + 4 * ys.length + 4 ≤ l →
    ∃ zs1 l2,
      mcIaddPre (l, mcHeader (s, xs), mcHeader (t, ys), xs, ys, zs) ∧
      mcIadd (l, mcHeader (s, xs), mcHeader (t, ys), xs, ys, zs) =
        (l2, mcHeader (mwiAdd (s, xs) (t, ys)), xs, ys, (mwiAdd (s, xs) (t, ys)).2 ++ zs1) ∧
      ((mwiAdd (s, xs) (t, ys)).2 ++ zs1).length = zs.length ∧
      l ≤ l2 + 4 * xs.length + 4 * ys.length + 4 := by
  rintro ⟨hx, hy, hz, okx, oky, hl⟩
  have hx' := lt_half_succ hx
  have hy' := lt_half_succ hy
  rw [mcIaddPre_def, mcIadd_def]
  simp only [mcHeader_EQ, mc_length hx, mc_length hy]
  by_cases hst : s = t
  · subst hst
    simp only [if_true, mcIadd1_def, mcHeader_AND_1]
    by_cases hlen : ys.length ≤ xs.length
    · have nlt : ¬ BitVec.ofNat width xs.length < BitVec.ofNat width ys.length := by
        rw [ofNat_lt_ofNat (by omega) (by omega)]; omega
      have la := length_mwAddv (xs := xs) (ys := ys) hlen
      obtain ⟨zs', zs2, rfl, hz'⟩ := less_eq_length zs (mwAddv xs ys false).length (by omega)
      obtain ⟨r1', r2', r8', r9', r10', l2, pre, eq, bound⟩ :=
        mcAdd_thm xs ys zs' zs2 l ⟨hlen, hz', by omega, by omega⟩
      simp only [nlt, if_false, eq, mcIadd3_def, if_true]
      refine ⟨zs2, l2, pre, ?_, ?_, by omega⟩
      · simp only [mwiAdd, if_true, hlen, shift_add_b2w]
      · simp only [mwiAdd, if_true, hlen, List.length_append]; omega
    · have lt : BitVec.ofNat width xs.length < BitVec.ofNat width ys.length := by
        rw [ofNat_lt_ofNat (by omega) (by omega)]; omega
      have la := length_mwAddv (xs := ys) (ys := xs) (by omega)
      obtain ⟨zs', zs2, rfl, hz'⟩ := less_eq_length zs (mwAddv ys xs false).length (by omega)
      obtain ⟨r1', r2', r8', r9', r10', l2, pre, eq, bound⟩ :=
        mcAdd_thm ys xs zs' zs2 l ⟨by omega, hz', by omega, by omega⟩
      have ne1 : (1 : BitVec width) ≠ 0 := by simp [NeZero.ne]
      simp only [lt, if_true, eq, mcIadd3_def, ne1, if_false]
      refine ⟨zs2, l2, pre, ?_, ?_, by omega⟩
      · simp only [mwiAdd, if_true, hlen, if_false, shift_add_b2w]
      · simp only [mwiAdd, if_true, hlen, if_false, List.length_append]; omega
  · obtain ⟨l2, pre, eq, bound⟩ :=
      mcCompare_thm (xs := xs) (ys := ys) (l := l) ⟨by omega, by omega, by omega⟩
    rw [mwCompare_thm xs ys ⟨okx, oky⟩] at eq
    simp only [hst, if_false, eq, mcHeader_AND_1]
    by_cases heq : mw2n xs = mw2n ys
    · simp only [heq, if_true, cmp2w]
      refine ⟨zs, l2, pre, ?_, ?_, by omega⟩
      · simp [mwiAdd, hst, heq, mcHeader]
      · simp [mwiAdd, hst, heq]
    · have ne1 : (1 : BitVec width) ≠ 0 := by simp [NeZero.ne]
      have hne : ¬ mw2n ys = mw2n xs := fun h => heq h.symm
      by_cases hlt : mw2n xs < mw2n ys
      · have lxy := mw2n_LESS xs ys ⟨okx, oky, by omega⟩
        obtain ⟨zs', zs2, rfl, hz'⟩ := less_eq_length zs ys.length (by omega)
        obtain ⟨r1', r2', r8', r9', r10', l3, pre3, eq3, bound3⟩ :=
          mcSub_thm ys xs zs' zs2 l2 ⟨lxy, hz', by omega, by omega⟩
        simp only [heq, hlt, if_false, cmp2w, decide_true, ne1, mcIadd2_def, if_true,
          mc_length hx, mc_length hy, eq3, mcIadd3_def]
        have ls := length_mwSubv ys xs lxy
        refine ⟨List.replicate (ys.length - (mwSubv ys xs).length) 0 ++ zs2, l3, ⟨pre, pre3⟩,
          ?_, ?_, by omega⟩
        · simp only [mwiAdd, hst, hne, if_false, Nat.not_le.mpr hlt, b2w_NOT, shift_add_b2w,
            List.append_assoc]
        · simp only [mwiAdd, hst, hne, if_false, Nat.not_le.mpr hlt, List.length_append,
            List.length_replicate]
          omega
      · have hgt : mw2n ys < mw2n xs := by omega
        have lyx := mw2n_LESS ys xs ⟨oky, okx, by omega⟩
        have xne : xs ≠ [] := by
          intro h; subst h; simp [mw2n] at hgt
        have w4 : 4 ≤ 2 ^ width := by
          have : 0 < xs.length := List.length_pos_iff.mpr xne
          omega
        have ne2 : (2 : BitVec width) ≠ 0 := by
          intro h; have := congrArg BitVec.toNat h
          simp [Nat.mod_eq_of_lt (show 2 < 2 ^ width by omega)] at this
        have ne21 : (2 : BitVec width) ≠ 1 := by
          intro h; have := congrArg BitVec.toNat h
          simp [Nat.mod_eq_of_lt (show 2 < 2 ^ width by omega),
            Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega)] at this
        obtain ⟨zs', zs2, rfl, hz'⟩ := less_eq_length zs xs.length (by omega)
        obtain ⟨r1', r2', r8', r9', r10', l3, pre3, eq3, bound3⟩ :=
          mcSub_thm xs ys zs' zs2 l2 ⟨lyx, hz', by omega, by omega⟩
        simp only [heq, hlt, if_false, cmp2w, decide_false, ne2, ne21, mcIadd2_def,
          mc_length hx, mc_length hy, eq3, mcIadd3_def, if_true]
        have ls := length_mwSubv xs ys lyx
        refine ⟨List.replicate (xs.length - (mwSubv xs ys).length) 0 ++ zs2, l3, ⟨pre, pre3⟩,
          ?_, ?_, by omega⟩
        · simp only [mwiAdd, hst, hne, if_false, Nat.le_of_lt hgt, if_true, shift_add_b2w,
            List.append_assoc]
        · simp only [mwiAdd, hst, hne, if_false, Nat.le_of_lt hgt, if_true, List.length_append,
            List.length_replicate]
          omega

end Flapjack.Misc.Multiword
