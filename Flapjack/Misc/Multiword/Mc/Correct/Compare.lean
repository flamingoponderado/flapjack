module

public import Flapjack.Misc.Multiword.Mc.Basics

@[expose] public section

/-! Correctness of the machine-code-style comparison functions of HOL's
`mc_multiword`. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- `mw_cmp` on lists extended at the most significant end (Flapjack helper). -/
theorem mwCmp_snoc {width : Nat} [NeZero width] (xs ys : List (BitVec width))
    (x y : BitVec width) :
    mwCmp (xs ++ [x]) (ys ++ [y]) =
      if x = y then mwCmp xs ys else some (decide (x < y)) := by
  rw [mwCmp]
  simp [holLast_append_singleton]

/-- `holEl` at the length of a prefix (Flapjack helper). -/
theorem holEl_append_length {α : Type} [Nonempty α] (xs ys : List α) (y : α) :
    holEl xs.length (xs ++ y :: ys) = y := by
  rw [holEl_eq_getElem _ _ (by simp)]
  simp

/-- A small numeral read back from a word (Flapjack helper). -/
theorem ofNat_toNat_of_lt {width n : Nat} (h : n < 2 ^ width) :
    (BitVec.ofNat width n).toNat = n := by
  simp [Nat.mod_eq_of_lt h]

/-- Decrementing a small nonzero numeral word (Flapjack helper). -/
theorem ofNat_succ_sub_one {width n : Nat} [NeZero width] (h : n + 1 < 2 ^ width) :
    BitVec.ofNat width (n + 1) - 1 = BitVec.ofNat width n := by
  have lt1 : (1 : Nat) < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le]
  · simp [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show n < 2 ^ width by omega), Nat.mod_eq_of_lt lt1]
  · rw [BitVec.le_def]
    simp [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt lt1]

/-- Incrementing a numeral word (Flapjack helper). -/
theorem ofNat_add_one {width : Nat} (n : Nat) :
    BitVec.ofNat width n + 1 = BitVec.ofNat width (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.add_mod]

/-- Equality of small numeral words (Flapjack helper). -/
theorem ofNat_inj {width a b : Nat} (ha : a < 2 ^ width) (hb : b < 2 ^ width) :
    BitVec.ofNat width a = BitVec.ofNat width b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [ofNat_toNat_of_lt ha, ofNat_toNat_of_lt hb] at this
  · rintro rfl; rfl

/-- Unsigned order of small numeral words (Flapjack helper). -/
theorem ofNat_lt_ofNat {width a b : Nat} (ha : a < 2 ^ width) (hb : b < 2 ^ width) :
    BitVec.ofNat width a < BitVec.ofNat width b ↔ a < b := by
  rw [BitVec.lt_def, ofNat_toNat_of_lt ha, ofNat_toNat_of_lt hb]

/-- A small successor numeral word is not one exactly when it is not zero
(Flapjack helper). -/
theorem ofNat_succ_eq_one {width n : Nat} (h : n + 1 < 2 ^ width) :
    BitVec.ofNat width (n + 1) = 1 ↔ n = 0 := by
  have lt1 : (1 : Nat) < 2 ^ width := by omega
  rw [show (1 : BitVec width) = BitVec.ofNat width 1 from rfl, ofNat_inj h lt1]
  omega

/-- A small numeral word is zero exactly at zero (Flapjack helper). -/
theorem ofNat_eq_zero {width n : Nat} (h : n < 2 ^ width) :
    BitVec.ofNat width n = 0 ↔ n = 0 := by
  rw [show (0 : BitVec width) = BitVec.ofNat width 0 from rfl, ofNat_inj h (by omega)]

/-- Updating the element after a prefix (Flapjack helper). -/
theorem set_append_length {α : Type} (xs ys : List α) (y v : α) :
    (xs ++ y :: ys).set xs.length v = xs ++ v :: ys := by
  simp

/-- The carry word of a boolean is nonzero exactly for true (Flapjack helper). -/
theorem decide_b2w_ne_zero {width : Nat} [NeZero width] (c : Bool) :
    decide ((b2w c : BitVec width) ≠ 0) = c := by
  have h := (b2w_eq (width := width) (w2 := width) (b := c)).1
  cases c
  · exact decide_eq_false (fun hne => hne (h.mpr (by simp)))
  · exact decide_eq_true (fun he => h.mp he rfl)

/-- A carry word is zero or one (Flapjack helper). -/
theorem b2w_zero_or_one {width : Nat} [NeZero width] (c : Bool) :
    (b2w c : BitVec width) ≠ 0 → (b2w c : BitVec width) = 1 := by
  cases c <;> simp [b2w, b2n]

/-- `single_add_word` on a carry word (Flapjack helper). -/
theorem singleAddWord_b2w {width : Nat} [NeZero width] (x y : BitVec width) (c : Bool) :
    singleAddWord x y (b2w c) = ((singleAdd x y c).1, b2w (singleAdd x y c).2) := by
  simp only [singleAddWord, decide_b2w_ne_zero]

/-- `single_sub_word` on a carry word (Flapjack helper). -/
theorem singleSubWord_b2w {width : Nat} [NeZero width] (x y : BitVec width) (c : Bool) :
    singleSubWord x y (b2w c) = ((singleSub x y c).1, b2w (singleSub x y c).2) := by
  simp only [singleSubWord, decide_b2w_ne_zero]

/-- Flapjack proof of the local HOL lemma `mc_cmp_thm` (before its
specialization to empty suffixes). -/
theorem mcCmp_thm_gen {width : Nat} [NeZero width] :
    ∀ (xs ys xs1 ys1 : List (BitVec width)) (l : Nat),
      ys.length = xs.length ∧ xs.length < 2 ^ width ∧ xs.length ≤ l →
      mcCmpPre (l, BitVec.ofNat width xs.length, xs ++ xs1, ys ++ ys1) ∧
      ∃ l2, mcCmp (l, BitVec.ofNat width xs.length, xs ++ xs1, ys ++ ys1) =
          (l2, cmp2w (mwCmp xs ys), xs ++ xs1, ys ++ ys1) ∧ l ≤ l2 + xs.length := by
  intro xs
  induction xs using snoc_induction with
  | nil =>
    intro ys xs1 ys1 l ⟨hl, _, _⟩
    have : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this
    refine ⟨by rw [mcCmpPre_def]; simp, l, ?_, by simp⟩
    rw [mcCmp_def, mwCmp]
    simp [cmp2w]
  | snoc xs x ih =>
    intro ys xs1 ys1 l ⟨hl, hlt, hle⟩
    obtain ⟨ys, y, rfl⟩ : ∃ ys2 y, ys = ys2 ++ [y] := by
      rcases List.eq_nil_or_concat ys with h | ⟨L, b, h⟩
      · subst h; simp at hl
      · exact ⟨L, b, by simpa using h⟩
    simp only [List.length_append, List.length_singleton] at hl hlt hle
    have hlen : ys.length = xs.length := by omega
    have ne : BitVec.ofNat width (xs.length + 1) ≠ 0 := by
      intro h
      have := congrArg BitVec.toNat h
      simp [Nat.mod_eq_of_lt hlt] at this
    have sub : BitVec.ofNat width (xs.length + 1) - 1 = BitVec.ofNat width xs.length := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le]
      · simp [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (show xs.length < 2 ^ width by omega),
          Nat.mod_eq_of_lt (Nat.one_lt_two_pow (NeZero.ne width))]
      · rw [BitVec.le_def]
        simp [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (NeZero.ne width))]
    have tn : (BitVec.ofNat width xs.length).toNat = xs.length := by
      simp [Nat.mod_eq_of_lt (show xs.length < 2 ^ width by omega)]
    have ex : holEl xs.length (xs ++ [x] ++ xs1) = x := by
      rw [List.append_assoc]; exact holEl_append_length _ _ _
    have ey : holEl xs.length (ys ++ [y] ++ ys1) = y := by
      rw [List.append_assoc, ← hlen]; exact holEl_append_length _ _ _
    have lx : xs.length < (xs ++ [x] ++ xs1).length := by simp
    have ly : xs.length < (ys ++ [y] ++ ys1).length := by simp; omega
    simp only [List.length_append, List.length_singleton]
    rw [mcCmpPre_def, mcCmp_def, mwCmp_snoc]
    simp only [if_neg ne, sub, tn, ex, ey]
    by_cases hxy : x = y
    · subst hxy
      have := ih ys (x :: xs1) (x :: ys1) (l - 1) ⟨hlen, by omega, by omega⟩
      simp only [List.append_assoc, List.singleton_append] at this ⊢
      obtain ⟨pre, l2, eq, bound⟩ := this
      simp only [↓reduceIte]
      refine ⟨⟨pre, ⟨by simp, by simp; omega⟩, by omega⟩, l2, eq, by omega⟩
    · simp only [if_neg hxy]
      refine ⟨?_, l, ?_, by omega⟩
      · split <;> exact ⟨lx, ly⟩
      · by_cases h : x < y <;> simp [h, cmp2w]

/-- Flapjack proof of the local HOL lemma `mc_cmp_thm`. -/
theorem mcCmp_thm {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)) (l : Nat),
      ys.length = xs.length ∧ xs.length < 2 ^ width ∧ xs.length ≤ l →
      mcCmpPre (l, BitVec.ofNat width xs.length, xs, ys) ∧
      ∃ l2, mcCmp (l, BitVec.ofNat width xs.length, xs, ys) =
          (l2, cmp2w (mwCmp xs ys), xs, ys) ∧ l ≤ l2 + xs.length := by
  intro xs ys l h
  simpa using mcCmp_thm_gen xs ys [] [] l h

/-- Flapjack proof of the local HOL lemma `mc_compare_thm`. -/
theorem mcCompare_thm {width : Nat} [NeZero width] {xs ys : List (BitVec width)} {l : Nat} :
    xs.length < 2 ^ width ∧ ys.length < 2 ^ width ∧ xs.length + 1 ≤ l →
    ∃ l2, mcComparePre (l, BitVec.ofNat width xs.length, BitVec.ofNat width ys.length, xs, ys) ∧
      mcCompare (l, BitVec.ofNat width xs.length, BitVec.ofNat width ys.length, xs, ys) =
        (l2, cmp2w (mwCompare xs ys), xs, ys) ∧ l ≤ l2 + xs.length + 1 := by
  rintro ⟨hx, hy, hl⟩
  have lt_iff : ∀ a b : Nat, a < 2 ^ width → b < 2 ^ width →
      (BitVec.ofNat width a < BitVec.ofNat width b ↔ a < b) := by
    intro a b ha hb
    rw [BitVec.lt_def]; simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [mcComparePre_def, mcCompare_def, mwCompare]
  by_cases h1 : xs.length < ys.length
  · simp [(lt_iff _ _ hx hy).mpr h1, h1, cmp2w]; omega
  by_cases h2 : ys.length < xs.length
  · have := (lt_iff _ _ hy hx).mpr h2
    simp [this, h1, h2, cmp2w, (lt_iff _ _ hx hy)]; omega
  have heq : xs.length = ys.length := by omega
  obtain ⟨pre, l2, eq, bound⟩ := mcCmp_thm xs ys (l - 1) ⟨heq.symm, hx, by omega⟩
  have n1 : ¬ BitVec.ofNat width xs.length < BitVec.ofNat width ys.length :=
    fun h => h1 ((lt_iff _ _ hx hy).mp h)
  have n2 : ¬ BitVec.ofNat width ys.length < BitVec.ofNat width xs.length :=
    fun h => h2 ((lt_iff _ _ hy hx).mp h)
  refine ⟨l2, ?_, ?_, by omega⟩
  · simp only [n1, n2, if_false]
    exact ⟨pre, by omega⟩
  · simp only [n1, n2, h1, h2, if_false, eq]

/-- Flapjack proof of the local HOL lemma `mc_header_sign`. -/
theorem mcHeader_sign {width : Nat} [NeZero width] {s : Bool} {xs : List (BitVec width)} :
    (mcHeader (s, xs) &&& 1 = (0 : BitVec width)) ↔ ¬ s = true := by
  rw [mcHeader_AND_1]
  exact (b2w_eq (w2 := width)).1

/-- The value of a header (Flapjack helper). -/
theorem mcHeader_toNat {width : Nat} [NeZero width] {s : Bool} {xs : List (BitVec width)}
    (h : xs.length < 2 ^ width / 2) :
    (mcHeader (s, xs)).toNat = xs.length * 2 + b2n s := by
  have pos := Nat.pos_of_ne_zero (NeZero.ne width)
  have two : 2 ^ width = 2 ^ width / 2 * 2 := by
    rw [Nat.div_mul_cancel]
    exact Nat.dvd_of_mod_eq_zero (by
      rw [show width = width - 1 + 1 by omega, Nat.pow_succ]; simp)
  have lt1 : (1 : Nat) < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  cases s
  · simp [mcHeader, b2n]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [mcHeader, if_true, b2n]
    have one : (1 : BitVec width).toNat = 1 := by simp [Nat.mod_eq_of_lt lt1]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, one, Nat.mod_eq_of_lt (a := xs.length * 2) (by omega),
      Nat.mod_eq_of_lt (by omega)]

/-- Flapjack proof of the local HOL lemma `mc_length`. -/
theorem mc_length {width : Nat} [NeZero width] {s : Bool} {xs : List (BitVec width)} :
    xs.length < 2 ^ width / 2 → mcHeader (s, xs) >>> 1 = BitVec.ofNat width xs.length := by
  intro h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, mcHeader_toNat h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  cases s
  · simp [b2n, Nat.shiftRight_eq_div_pow]
  · simp [b2n, Nat.shiftRight_eq_div_pow]; omega

/-- `option_eq F` is the identity (Flapjack helper). -/
theorem optionEq_false (o : Option Bool) : optionEq false o = o := by
  rcases o with _ | _ | _ <;> simp [optionEq]

/-- Flapjack proof of the local HOL lemma `mc_icompare_thm`. -/
theorem mcIcompare_thm {width : Nat} [NeZero width] {s t : Bool}
    {xs ys : List (BitVec width)} {l : Nat} :
    xs.length < 2 ^ width / 2 ∧ ys.length < 2 ^ width / 2 ∧ xs.length + 1 ≤ l →
    ∃ l2, mcIcomparePre (l, mcHeader (s, xs), mcHeader (t, ys), xs, ys) ∧
      mcIcompare (l, mcHeader (s, xs), mcHeader (t, ys), xs, ys) =
        (l2, cmp2w (mwiCompare (s, xs) (t, ys)), xs, ys) ∧ l ≤ l2 + xs.length + 1 := by
  rintro ⟨hx, hy, hl⟩
  obtain ⟨l2, pre, eq, bound⟩ :=
    mcCompare_thm (xs := xs) (ys := ys) (l := l) ⟨by omega, by omega, hl⟩
  rw [mcIcomparePre_def, mcIcompare_def]
  simp only [mcHeader_sign, mc_length hx, mc_length hy, eq]
  cases s <;> cases t <;> simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false,
    mwiCompare, ↓reduceIte]
  · exact ⟨l2, pre, by rw [optionEq_false], bound⟩
  · exact ⟨l, trivial, by simp [cmp2w], by omega⟩
  · exact ⟨l, trivial, by simp [cmp2w], by omega⟩
  · refine ⟨l2, ?_, ?_, bound⟩
    · split <;> exact pre
    · by_cases w1 : width = 1
      · subst w1
        have ex : xs = [] := List.eq_nil_of_length_eq_zero (by have : 2 ^ 1 / 2 = 1 := rfl; omega)
        have ey : ys = [] := List.eq_nil_of_length_eq_zero (by have : 2 ^ 1 / 2 = 1 := rfl; omega)
        subst ex; subst ey
        simp [mwCompare, mwCmp, optionEq, cmp2w]
      · have w2 : 2 ≤ width := by have := NeZero.ne width; omega
        have p4 : 4 ≤ 2 ^ width := by
          calc 4 = 2 ^ 2 := rfl
            _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) w2
        have c1 : (BitVec.ofNat width 1 : BitVec width) ≠ 0 := by
          intro h; have := congrArg BitVec.toNat h; simp [Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega)] at this
        have c2 : (BitVec.ofNat width 2 : BitVec width) ≠ 0 := by
          intro h; have := congrArg BitVec.toNat h; simp [Nat.mod_eq_of_lt (show 2 < 2 ^ width by omega)] at this
        have x1 : (1 : BitVec width) ^^^ 3 = 2 := by
          apply BitVec.eq_of_toNat_eq
          simp [Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega), Nat.mod_eq_of_lt (show 3 < 2 ^ width by omega),
            Nat.mod_eq_of_lt (show 2 < 2 ^ width by omega)]
        have x2 : (2 : BitVec width) ^^^ 3 = 1 := by
          apply BitVec.eq_of_toNat_eq
          simp [Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega), Nat.mod_eq_of_lt (show 3 < 2 ^ width by omega),
            Nat.mod_eq_of_lt (show 2 < 2 ^ width by omega)]
        rcases mwCompare xs ys with _ | _ | _ <;> simp_all [cmp2w, optionEq]

end Flapjack.Misc.Multiword
