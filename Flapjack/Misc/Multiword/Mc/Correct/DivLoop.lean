module

public import Flapjack.Misc.Multiword.Mc.Correct.DivAdjust

@[expose] public section

/-! Correctness of the machine-code-style main division loop of HOL's
`mc_multiword`. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Adding numeral words (Flapjack helper). -/
theorem ofNat_add_ofNat {width : Nat} (a b : Nat) :
    BitVec.ofNat width a + BitVec.ofNat width b = BitVec.ofNat width (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.add_mod]

/-- Subtracting small numeral words (Flapjack helper). -/
theorem ofNat_sub_ofNat {width a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ width) :
    BitVec.ofNat width a - BitVec.ofNat width b = BitVec.ofNat width (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ofNat_toNat_of_lt ha,
    ofNat_toNat_of_lt (by omega)]; exact hb), ofNat_toNat_of_lt ha,
    ofNat_toNat_of_lt (by omega), ofNat_toNat_of_lt (by omega)]

/-- Subtracting one from a small numeral word (Flapjack helper). -/
theorem ofNat_sub_one {width a : Nat} (h1 : 1 ≤ a) (ha : a < 2 ^ width) :
    BitVec.ofNat width a - 1 = BitVec.ofNat width (a - 1) :=
  ofNat_sub_ofNat (b := 1) h1 ha

/-- A list of length at least three ends in three digits (Flapjack helper). -/
theorem exists_three_last {α : Type} (W : List α) (h : 3 ≤ W.length) :
    ∃ A a3 a2 a1, W = A ++ [a3, a2, a1] := by
  refine ⟨W.take (W.length - 3), W[W.length - 3], W[W.length - 2], W[W.length - 1], ?_⟩
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_append, List.length_take]
    split
    · simp
    · rename_i hi
      simp only [Nat.min_eq_left (by omega : W.length - 3 ≤ W.length)] at hi ⊢
      have : i - (W.length - 3) < 3 := by simp at h2; omega
      rcases (by omega : i - (W.length - 3) = 0 ∨ i - (W.length - 3) = 1 ∨
        i - (W.length - 3) = 2) with e | e | e <;> simp only [e] <;>
        (simp; congr 1; omega)

/-- A list of length at least two ends in two digits (Flapjack helper). -/
theorem exists_two_last {α : Type} (W : List α) (h : 2 ≤ W.length) :
    ∃ B b2 b1, W = B ++ [b2, b1] := by
  refine ⟨W.take (W.length - 2), W[W.length - 2], W[W.length - 1], ?_⟩
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_append, List.length_take]
    split
    · simp
    · rename_i hi
      simp only [Nat.min_eq_left (by omega : W.length - 2 ≤ W.length)] at hi ⊢
      have : i - (W.length - 2) < 2 := by simp at h2; omega
      rcases (by omega : i - (W.length - 2) = 0 ∨ i - (W.length - 2) = 1) with e | e <;>
        simp only [e] <;> (simp; congr 1; omega)

/-- `holEl` past a prefix (Flapjack helper). -/
theorem holEl_append_prefix {α : Type} [Nonempty α] (xs ys : List α) (i : Nat) :
    holEl (xs.length + i) (xs ++ ys) = holEl i ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.cons_append]
    rw [show xs.length + 1 + i = (xs.length + i) + 1 by omega, holEl_cons_succ, ih]

/-- Flapjack proof of the local HOL lemma `mc_div_loop_thm` (its unused
universally quantified variables are omitted). -/
theorem mcDivLoop_thm {width : Nat} [NeZero width] {d : BitVec width}
    {ys : List (BitVec width)} :
    ∀ (zs1 zs zs2 : List (BitVec width)) (l : Nat),
      zs.length = ys.length ∧ (zs1 ++ zs ++ zs2).length < 2 ^ width ∧ 1 < ys.length ∧
      holLast (mwMulBySingle d ys).dropLast ≠ 0 ∧
      zs1.length * (2 ^ width + 2 * ys.length + 4) ≤ l →
      ∃ l2,
        mcDivLoopPre (l, d, BitVec.ofNat width ys.length, BitVec.ofNat width zs1.length,
          BitVec.ofNat width ys.length, holLast (mwMulBySingle d ys).dropLast,
          holLast (mwMulBySingle d ys).dropLast.dropLast, ys, zs1 ++ zs ++ zs2) ∧
        mcDivLoop (l, d, BitVec.ofNat width ys.length, BitVec.ofNat width zs1.length,
          BitVec.ofNat width ys.length, holLast (mwMulBySingle d ys).dropLast,
          holLast (mwMulBySingle d ys).dropLast.dropLast, ys, zs1 ++ zs ++ zs2) =
          (l2, d, BitVec.ofNat width ys.length, 0, BitVec.ofNat width ys.length,
            holLast (mwMulBySingle d ys).dropLast,
            holLast (mwMulBySingle d ys).dropLast.dropLast, ys,
            (mwDivAux zs1 zs (mwMulBySingle d ys).dropLast).2 ++
              (mwDivAux zs1 zs (mwMulBySingle d ys).dropLast).1.reverse ++ zs2) ∧
        l ≤ l2 + zs1.length * (2 ^ width + 2 * ys.length + 4) := by
  intro zs1
  induction zs1 using snoc_induction with
  | nil =>
    intro zs zs2 l _
    refine ⟨l, ?_, ?_, by simp⟩
    · rw [mcDivLoopPre_def]; simp
    · rw [mcDivLoop_def, mwDivAux]; simp
  | snoc zs1 x ih =>
    intro zs zs2 l ⟨hz, hlen, hy, hv, hl⟩
    simp only [List.length_append, List.length_singleton] at hlen hl ⊢
    have hmul : (zs1.length + 1) * (2 ^ width + 2 * ys.length + 4) =
        zs1.length * (2 ^ width + 2 * ys.length + 4) + (2 ^ width + 2 * ys.length + 4) := by
      ring
    rw [hmul] at hl ⊢
    have hYlen : (mwMulBySingle d ys).dropLast.length = ys.length := by
      rw [List.length_dropLast, length_mwMulBySingle]; omega
    obtain ⟨B, b2, b1, hY⟩ := exists_two_last (mwMulBySingle d ys).dropLast (by omega)
    have hb1 : holLast (mwMulBySingle d ys).dropLast = b1 := by
      rw [hY, show B ++ [b2, b1] = (B ++ [b2]) ++ [b1] by simp, holLast_append_singleton]
    have hb2 : holLast (mwMulBySingle d ys).dropLast.dropLast = b2 := by
      rw [hY, show B ++ [b2, b1] = (B ++ [b2]) ++ [b1] by simp, List.dropLast_concat,
        holLast_append_singleton]
    have hYr : (mwMulBySingle d ys).dropLast.reverse = b1 :: b2 :: B.reverse := by
      rw [hY]; simp
    obtain ⟨A, a3, a2, a1, hW⟩ := exists_three_last (x :: zs) (by simp; omega)
    have hA : A.length + 2 = ys.length := by
      have := congrArg List.length hW; simp at this; omega
    have hWr : (x :: zs).reverse = a1 :: a2 :: a3 :: A.reverse := by rw [hW]; simp
    have hL : zs1 ++ x :: (zs ++ zs2) = zs1 ++ (A ++ a3 :: a2 :: a1 :: zs2) := by
      rw [show x :: (zs ++ zs2) = (x :: zs) ++ zs2 by simp, hW]; simp
    -- the three leading window digits
    have el1 : holEl (zs1.length + (A.length + 2)) (zs1 ++ x :: (zs ++ zs2)) = a1 := by
      rw [hL, holEl_append_prefix, holEl_append_prefix]; rfl
    have el2 : holEl (zs1.length + (A.length + 1)) (zs1 ++ x :: (zs ++ zs2)) = a2 := by
      rw [hL, holEl_append_prefix, holEl_append_prefix]; rfl
    have el3 : holEl (zs1.length + (A.length + 0)) (zs1 ++ x :: (zs ++ zs2)) = a3 := by
      rw [hL, holEl_append_prefix, holEl_append_prefix]; rfl
    -- the word arithmetic on the index register
    have B0 : zs1.length + 1 + ys.length < 2 ^ width := by omega
    have e0 : BitVec.ofNat width (zs1.length + 1) + BitVec.ofNat width ys.length - 1 =
        BitVec.ofNat width (zs1.length + (A.length + 2)) := by
      rw [ofNat_add_ofNat, ofNat_sub_one (by omega) (by omega)]; congr 1; omega
    have e1 : BitVec.ofNat width (zs1.length + (A.length + 2)) - 1 =
        BitVec.ofNat width (zs1.length + (A.length + 1)) := by
      rw [ofNat_sub_one (by omega) (by omega)]; congr 1
    have e2 : BitVec.ofNat width (zs1.length + (A.length + 1)) - 1 =
        BitVec.ofNat width (zs1.length + (A.length + 0)) := by
      rw [ofNat_sub_one (by omega) (by omega)]; congr 1
    have t0 : (BitVec.ofNat width (zs1.length + (A.length + 2))).toNat =
        zs1.length + (A.length + 2) := ofNat_toNat_of_lt (by omega)
    have t1 : (BitVec.ofNat width (zs1.length + (A.length + 1))).toNat =
        zs1.length + (A.length + 1) := ofNat_toNat_of_lt (by omega)
    have t2 : (BitVec.ofNat width (zs1.length + (A.length + 0))).toNat =
        zs1.length + (A.length + 0) := ofNat_toNat_of_lt (by omega)
    have e3 : BitVec.ofNat width (zs1.length + 1) - 1 = BitVec.ofNat width zs1.length := by
      rw [ofNat_sub_one (by omega) (by omega)]; rfl
    have ne0 : BitVec.ofNat width (zs1.length + 1) ≠ 0 := by
      rw [Ne, ofNat_eq_zero (by omega)]; omega
    -- the guess
    obtain ⟨l1, pre1, eq1, bound1⟩ :=
      mcDivGuess_thm (us := A.reverse) (vs := B.reverse) (l := l)
        a1 a2 a3 (holLast (mwMulBySingle d ys).dropLast)
        (holLast (mwMulBySingle d ys).dropLast.dropLast) (by
          have : 2 ^ width + 1 ≤ 2 ^ width + 2 * ys.length + 4 := by omega
          omega)
    have hguess : mwDivGuess (a1 :: a2 :: a3 :: A.reverse)
        (holLast (mwMulBySingle d ys).dropLast :: holLast (mwMulBySingle d ys).dropLast.dropLast ::
          B.reverse) = mwDivGuess (x :: zs).reverse (mwMulBySingle d ys).dropLast.reverse := by
      rw [hWr, hYr, hb1, hb2]
    rw [hguess] at eq1
    -- the adjustment
    obtain ⟨l2, pre2, eq2, bound2⟩ :=
      mcDivAdjust_thm (r6 := d) (r7 := mwDivGuess (x :: zs).reverse (mwMulBySingle d ys).dropLast.reverse)
        (ys := ys) (zs := x :: zs) (zs1 := zs1) (zs2 := zs2) (l := l1)
        ⟨by simp; omega, by omega, by simp; omega, by omega⟩
    simp only [List.length_append, List.length_cons, hz] at eq2 pre2 bound2
    generalize hadj : mwDivAdjust (mwDivGuess (x :: zs).reverse (mwMulBySingle d ys).dropLast.reverse)
      (x :: zs) (mwMulBySingle d ys).dropLast = adj at eq2
    have e4 : BitVec.ofNat width (zs1.length + (ys.length + 1)) - BitVec.ofNat width ys.length - 1 =
        BitVec.ofNat width zs1.length := by
      rw [ofNat_sub_ofNat (by omega) (by omega), ofNat_sub_one (by omega) (by omega)]
      congr 1; omega
    -- the multiply-subtract
    obtain ⟨l3, pre3, eq3, bound3⟩ :=
      mcDivSubLoop_thm (r6 := d) (r7 := adj) ys (x :: zs) zs1 zs2 (l2 - 1)
        ⟨by simp; omega, by omega, by simp; omega, by omega⟩
    rw [mwMulBySingle2_thm] at eq3
    simp only [List.length_append, List.length_cons, hz] at eq3
    generalize hS : (mwSub (x :: zs) (mwMulBySingle adj (mwMulBySingle d ys).dropLast) true).1 = S
      at eq3
    have hSlen : S.length = ys.length + 1 := by
      rcases h : mwSub (x :: zs) (mwMulBySingle adj (mwMulBySingle d ys).dropLast) true with ⟨q, c⟩
      have := length_mwSub _ _ _ _ _ h
      rw [h] at hS; simp at hS; subst hS; simp at this; omega
    obtain ⟨S', s1, rfl⟩ : ∃ S' s1, S = S' ++ [s1] := by
      rcases List.eq_nil_or_concat S with e | ⟨L, b, e⟩
      · subst e; simp at hSlen
      · exact ⟨L, b, by simpa using e⟩
    simp only [List.length_append, List.length_singleton] at hSlen
    have e5 : BitVec.ofNat width (zs1.length + (ys.length + 1)) - 1 =
        BitVec.ofNat width (zs1.length + ys.length) := by
      rw [ofNat_sub_one (by omega) (by omega)]; congr 1
    have t5 : (BitVec.ofNat width (zs1.length + ys.length)).toNat = zs1.length + ys.length :=
      ofNat_toNat_of_lt (by omega)
    have e6 : BitVec.ofNat width (zs1.length + ys.length) - BitVec.ofNat width ys.length =
        BitVec.ofNat width zs1.length := by
      rw [ofNat_sub_ofNat (by omega) (by omega)]; congr 1; omega
    have hset : (zs1 ++ (S' ++ [s1]) ++ zs2).set (zs1.length + ys.length) adj =
        zs1 ++ S' ++ adj :: zs2 := by
      rw [show zs1 ++ (S' ++ [s1]) ++ zs2 = (zs1 ++ S') ++ s1 :: zs2 by simp,
        show zs1.length + ys.length = (zs1 ++ S').length by simp; omega, set_append_length]
    -- the recursive call
    obtain ⟨l4, pre4, eq4, bound4⟩ :=
      ih S' (adj :: zs2) (l3 - 1) ⟨by omega, by simp; omega, hy, hv, by omega⟩
    have hdiv : mwDivAux (zs1 ++ [x]) zs (mwMulBySingle d ys).dropLast =
        (adj :: (mwDivAux zs1 S' (mwMulBySingle d ys).dropLast).1,
          (mwDivAux zs1 S' (mwMulBySingle d ys).dropLast).2) := by
      rw [mwDivAux]
      simp only [List.append_eq_nil_iff, List.cons_ne_nil, and_false, if_false,
        holLast_append_singleton, List.dropLast_concat, hadj, hS]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
      at eq2 pre2 eq3 pre3 eq4 pre4 hset ⊢
    refine ⟨l4, ?_, ?_, by omega⟩
    · rw [mcDivLoopPre_def]
      simp only [ne0, if_false, e0, t0, el1, e1, t1, el2, e2, t2, el3, eq1, e3, eq2, e4, eq3,
        e5, t5, hset, e6]
      refine ⟨pre4, ⟨⟨⟨⟨⟨⟨by simp; omega, by simp; omega⟩, by simp; omega⟩,
        pre1.mpr (fun _ => hv)⟩, pre2⟩, pre3, by omega⟩, by simp; omega⟩, by omega⟩
    · rw [mcDivLoop_def]
      simp only [ne0, if_false, e0, t0, el1, e1, t1, el2, e2, t2, el3, eq1, e3, eq2, e4, eq3,
        e5, t5, hset, e6, eq4, hdiv]
      simp

end Flapjack.Misc.Multiword
