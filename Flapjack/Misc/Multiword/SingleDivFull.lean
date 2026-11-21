module

public import Flapjack.Misc.Multiword.Shift
public import Flapjack.Misc.Multiword.Compare
public import Flapjack.Misc.Multiword.AddSub
public import Flapjack.Misc.Multiword.DivSingle
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Shift-and-subtract implementation of `single_div` for architectures
without a division instruction (the last section of HOL's `multiwordScript`). -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Bit-serial long division on numbers. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "num_div_loop_def"]
def numDivLoop : Nat × Nat × Nat × Nat → Nat × Nat
  | (k, n, m, i) =>
    if k = 0 then (m, i) else
      let n := n / 2
      let m := m * 2
      if i < n then
        numDivLoop (k - 1, n, m, i)
      else
        numDivLoop (k - 1, n, m + 1, i - n)
termination_by a => a.1
decreasing_by all_goals omega

private theorem numDivLoop_lemma :
    ∀ (k i n m : Nat), i < n * 2 ^ k → 0 < n →
      numDivLoop (k, n * 2 ^ k, m, i) = (m * 2 ^ k + i / n, i % n) := by
  intro k
  induction k with
  | zero =>
    intro i n m hi hn
    rw [numDivLoop]
    simp only [Nat.pow_zero, Nat.mul_one, if_true] at hi ⊢
    rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, Nat.add_zero]
  | succ k ih =>
    intro i n m hi hn
    rw [numDivLoop]
    have hk : n * 2 ^ (k + 1) / 2 = n * 2 ^ k := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]
    simp only [Nat.add_one_ne_zero, if_false, hk, Nat.add_sub_cancel]
    have p : 0 < 2 ^ k := Nat.two_pow_pos k
    split
    · rename_i lt
      rw [ih i n (m * 2) lt hn]
      have : i / n < 2 ^ k := (Nat.div_lt_iff_lt_mul hn).2 (by rw [Nat.mul_comm]; exact lt)
      simp only [Prod.mk.injEq, and_true]
      rw [Nat.pow_succ]; ring
    · rename_i ge
      have ge' : n * 2 ^ k ≤ i := Nat.le_of_not_lt ge
      have lt : i - n * 2 ^ k < n * 2 ^ k := by
        rw [Nat.pow_succ, ← Nat.mul_assoc] at hi; omega
      rw [ih (i - n * 2 ^ k) n (m * 2 + 1) lt hn]
      have hdiv : (i - n * 2 ^ k) / n = i / n - 2 ^ k := by
        exact Nat.sub_mul_div i n (2 ^ k)
      have hmod : (i - n * 2 ^ k) % n = i % n := Nat.sub_mul_mod ge'
      have hle : 2 ^ k ≤ i / n := (Nat.le_div_iff_mul_le hn).2 (by rw [Nat.mul_comm]; exact ge')
      rw [hdiv, hmod, Nat.pow_succ]
      simp only [Prod.mk.injEq, and_true]
      have : m * 2 * 2 ^ k + 2 ^ k + (i / n - 2 ^ k) = m * 2 * 2 ^ k + i / n := by omega
      rw [Nat.add_mul, Nat.one_mul, this]; ring

/-- Starting from a zero quotient, `num_div_loop` computes division and remainder. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "num_div_loop_thm"]
theorem numDivLoop_thm {i n k : Nat} :
    i < n * 2 ^ k ∧ 0 < n → numDivLoop (k, n * 2 ^ k, 0, i) = (i / n, i % n) := by
  rintro ⟨hi, hn⟩
  rw [numDivLoop_lemma k i n 0 hi hn, Nat.zero_mul, Nat.zero_add]

private theorem sub_one_toNat_lt {width : Nat} [NeZero width] {k : BitVec width} (h : ¬k = 0) :
    (k - 1).toNat < k.toNat := by
  have : k.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  have pos := Nat.pos_of_ne_zero (NeZero.ne width)
  have one : (1 : BitVec width).toNat = 1 := by
    simp [BitVec.toNat_ofNat, Nat.one_mod_two_pow_eq_one.2 pos]
  rw [BitVec.toNat_sub, one]
  have hk := k.isLt
  rw [show 2 ^ width - 1 + k.toNat = (k.toNat - 1) + 2 ^ width by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- Word-level shift-and-subtract division loop over two-digit numbers. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "single_div_loop_def"
  (words_as_type_indexed_bitvec)]
noncomputable def singleDivLoop {width : Nat} [NeZero width] :
    BitVec width × List (BitVec width) × BitVec width × List (BitVec width) →
      BitVec width × List (BitVec width)
  | (k, ns, m, is) =>
    if k = 0 then (m, is) else
      let ns := mwShift ns
      let m := m <<< 1
      if mwCmp is ns = some true then
        singleDivLoop (k - 1, ns, m, is)
      else
        let m := m + 1
        let (is, _) := mwSub is ns true
        singleDivLoop (k - 1, ns, m, is)
termination_by a => a.1.toNat
decreasing_by all_goals exact sub_one_toNat_lt ‹_›

/-- `single_div` computed by `single_div_loop`; `HD` is the reviewed `holHd`. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "single_div_full_def"
  (words_as_type_indexed_bitvec)]
noncomputable def singleDivFull {width : Nat} [NeZero width] (m2 m1 n : BitVec width) :
    BitVec width × BitVec width :=
  let (m, is) := singleDivLoop (BitVec.ofNat width width, [0, n], 0, [m1, m2])
  (m, holHd is)

/-- The numeral power bound. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LESS_2_EXP"]
theorem LESS_2_EXP : ∀ n : Nat, n < 2 ^ n := fun _ => Nat.lt_two_pow_self

/-- Values of an empty list and of a list with a zero least-significant digit; the
two conjuncts carry independent word dimensions in the original. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw2n_0"
  (words_as_type_indexed_bitvec)]
theorem mw2n_0 {w1 : Nat} {w2 : Nat} [NeZero w1] [NeZero w2] (xs : List (BitVec w2)) :
    mw2n ([] : List (BitVec w1)) = 0 ∧ mw2n ((0 : BitVec w2) :: xs) = 2 ^ w2 * mw2n xs := by
  simp [mw2n]

/-- A nonempty list whose value fits one word has that value as its head. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "HD_eq_n2w_mw2n"
  (words_as_type_indexed_bitvec)]
theorem HD_eq_n2w_mw2n {width : Nat} [NeZero width] {xs : List (BitVec width)} :
    xs.length ≠ 0 ∧ mw2n xs < 2 ^ width → holHd xs = BitVec.ofNat width (mw2n xs) := by
  rintro ⟨len, lt⟩
  cases xs with
  | nil => simp at len
  | cons x t =>
    simp only [holHd, mw2n] at lt ⊢
    have : mw2n t = 0 := by
      rcases Nat.eq_zero_or_pos (mw2n t) with h | h
      · exact h
      · exfalso
        have := Nat.le_mul_of_pos_right (2 ^ width) h
        omega
    rw [this, Nat.mul_zero, Nat.add_zero]
    simp

private theorem mw2n_two {width : Nat} [NeZero width] (a b : BitVec width) :
    mw2n [a, b] = a.toNat + 2 ^ width * b.toNat := by
  simp [mw2n]

private theorem singleDivLoop_thm {width : Nat} [NeZero width] :
    ∀ (k : Nat) (ns : List (BitVec width)) (m : BitVec width) (is : List (BitVec width))
      (t : BitVec width) (qs : List (BitVec width)),
      singleDivLoop (BitVec.ofNat width k, ns, m, is) = (t, qs) →
      k < 2 ^ width → k ≤ width → m.toNat < 2 ^ (width - k) →
      ns.length = 2 → is.length = 2 →
      numDivLoop (k, mw2n ns, m.toNat, mw2n is) = (t.toNat, mw2n qs) ∧ qs.length = 2 := by
  intro k
  induction k with
  | zero =>
    intro ns m is t qs h _ _ _ _ hl
    rw [singleDivLoop] at h
    simp only [BitVec.ofNat_eq_ofNat] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rw [numDivLoop]
    exact ⟨by simp, hl⟩
  | succ k ih =>
    intro ns m is t qs h hk hkw hm hns his
    have ne : ¬ BitVec.ofNat width (k + 1) = 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
      simp at this
    have km1 : BitVec.ofNat width (k + 1) - 1 = BitVec.ofNat width k := by
      rw [← BitVec.ofNat_add_ofNat]; exact BitVec.add_sub_cancel _ _
    rw [singleDivLoop] at h
    simp only [ne, km1] at h
    rw [numDivLoop]
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    have hsh := mwShift_thm ns
    have lsh : (mwShift ns).length = 2 := by rw [length_mwShift]; exact hns
    have cmp := mwCmpThm is (mwShift ns) (by rw [lsh, his])
    have wpos : 2 ^ (width - (k + 1)) * 2 = 2 ^ (width - k) := by
      rw [← Nat.pow_succ]; congr 1; omega
    have wle : 2 ^ (width - k) ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega)
    have mshift : (m <<< 1).toNat = m.toNat * 2 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
      exact Nat.mod_eq_of_lt (by omega)
    have hk' : k < 2 ^ width := by omega
    by_cases lt : mw2n is < mw2n ns / 2
    · have c : mwCmp is (mwShift ns) = some true := by
        rw [cmp, hsh]; simp [lt, Nat.ne_of_lt lt]
      simp only [c, if_true] at h
      rw [if_pos lt]
      have := ih (mwShift ns) (m <<< 1) is t qs h hk' (by omega) (by rw [mshift]; omega) lsh his
      rw [hsh, mshift] at this
      exact this
    · have c : ¬ mwCmp is (mwShift ns) = some true := by
        rw [cmp, hsh]; split <;> simp [lt]
      simp only [c, if_false] at h
      rw [if_neg lt]
      rcases hs : mwSub is (mwShift ns) true with ⟨is', d⟩
      rw [hs] at h
      have len' : is'.length = 2 := by
        have := (mwSub_lemma is (mwShift ns) true is' d ⟨hs, by rw [lsh, his]⟩).2
        rw [this, his]
      have val : mw2n is' = mw2n is - mw2n ns / 2 := by
        have := mwSub_thm is (mwShift ns) (by rw [lsh, his]) (by rw [hsh]; omega)
        rw [hs] at this; rw [← hsh]; exact this
      have m1 : (m <<< 1 + 1).toNat = m.toNat * 2 + 1 := by
        rw [BitVec.toNat_add, mshift]
        have pos := Nat.pos_of_ne_zero (NeZero.ne width)
        rw [show (1 : BitVec width).toNat = 1 by simp [Nat.one_mod_two_pow_eq_one.2 pos]]
        exact Nat.mod_eq_of_lt (by omega)
      have := ih (mwShift ns) (m <<< 1 + 1) is' t qs h hk' (by omega) (by rw [m1]; omega)
        lsh len'
      rw [hsh, m1, val] at this
      exact this

/-- Without overflow, the shift-and-subtract loop agrees with `single_div`. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "single_div_full_thm"
  (words_as_type_indexed_bitvec)]
theorem singleDivFull_thm {width : Nat} [NeZero width] {x1 x2 y : BitVec width} :
    mw2n [x2, x1] < mw2n [0, y] → singleDivFull x1 x2 y = singleDiv x1 x2 y := by
  intro hlt
  have z : (0 : BitVec width).toNat = 0 := by simp
  have h0y : mw2n [(0 : BitVec width), y] = y.toNat * 2 ^ width := by
    rw [mw2n_two, z, Nat.zero_add, Nat.mul_comm]
  have hi : mw2n [x2, x1] = x1.toNat * 2 ^ width + x2.toNat := by
    rw [mw2n_two]; ring
  rw [h0y, hi] at hlt
  have pos := Nat.pos_of_ne_zero (NeZero.ne width)
  have hy : 0 < y.toNat := by
    rcases Nat.eq_zero_or_pos y.toNat with h | h
    · rw [h, Nat.zero_mul] at hlt; omega
    · exact h
  unfold singleDivFull
  rcases hl : singleDivLoop (BitVec.ofNat width width, [0, y], 0, [x2, x1]) with ⟨t, qs⟩
  obtain ⟨eq, len⟩ := singleDivLoop_thm width [0, y] 0 [x2, x1] t qs hl
    Nat.lt_two_pow_self (Nat.le_refl _) (by simp) rfl rfl
  rw [h0y, hi, z, numDivLoop_thm ⟨hlt, hy⟩, Prod.mk.injEq] at eq
  obtain ⟨ht, hq⟩ := eq
  have hd : holHd qs = BitVec.ofNat width (mw2n qs) := by
    apply HD_eq_n2w_mw2n
    refine ⟨by rw [len]; decide, ?_⟩
    rw [← hq]
    exact Nat.lt_trans (Nat.mod_lt _ hy) y.isLt
  simp only [singleDiv, hd, ← hq, ht, Prod.mk.injEq, and_true]
  apply BitVec.eq_of_toNat_eq
  simp

end Flapjack.Misc.Multiword
