module

public import Flapjack.Misc.Multiword.Digits
public import Flapjack.Misc.Multiword.Length

@[expose] public section

/-! Multiword addition and subtraction, unsigned and signed. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Add equal-length digit lists with carry; HOL's `HD`/`TL` read the second list. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_add_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwAdd {width : Nat} [NeZero width] :
    List (BitVec width) → List (BitVec width) → Bool → List (BitVec width) × Bool
  | [], _, c => ([], c)
  | x :: xs, ys, c =>
    let (z, c1) := singleAdd x (holHd ys) c
    let (zs, c2) := mwAdd xs ys.tail c1
    (z :: zs, c2)

/-- Subtract digit lists with borrow, treating a missing second digit as zero. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_sub_def"
  (words_as_type_indexed_bitvec)]
def mwSub {width : Nat} [NeZero width] :
    List (BitVec width) → List (BitVec width) → Bool → List (BitVec width) × Bool
  | [], _, c => ([], c)
  | x :: xs, [], c =>
    let (z, c1) := singleSub x 0 c
    let (zs, c2) := mwSub xs [] c1
    (z :: zs, c2)
  | x :: xs, y :: ys, c =>
    let (z, c1) := singleSub x y c
    let (zs, c2) := mwSub xs ys c1
    (z :: zs, c2)

/-- Single-word addition computes the sum with the carry as the high digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "single_add_thm"
  (words_as_type_indexed_bitvec)]
theorem singleAdd_thm {width : Nat} [NeZero width] :
    ∀ (x y z : BitVec width) (c d : Bool), singleAdd x y c = (z, d) →
      z.toNat + 2 ^ width * b2n d = x.toNat + y.toNat + b2n c := by
  intro x y z c d h
  simp only [singleAdd, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hw : 1 < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  have hb : b2n c ≤ 1 := by cases c <;> simp [b2n]
  have hbw : (b2w c : BitVec width).toNat = b2n c := by
    simp only [b2w, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add, hbw, Nat.mod_add_mod]
  have bound : x.toNat + y.toNat + b2n c < 2 ^ width + 2 ^ width := by omega
  generalize x.toNat + y.toNat + b2n c = S at bound ⊢
  by_cases big : 2 ^ width ≤ S
  · rw [decide_eq_true big, Nat.mod_eq_sub_mod big, Nat.mod_eq_of_lt (by omega)]
    simp only [b2n]; omega
  · rw [decide_eq_false big, Nat.mod_eq_of_lt (by omega)]
    simp only [b2n]; omega

private theorem singleSub_thm {width : Nat} [NeZero width] (x y z : BitVec width) (c d : Bool)
    (h : singleSub x y c = (z, d)) :
    z.toNat + 2 ^ width * b2n d + y.toNat = x.toNat + b2n c + (2 ^ width - 1) := by
  have := singleAdd_thm x (~~~y) z c d h
  have hy := y.isLt
  rw [BitVec.toNat_not] at this
  omega

/-- Subtraction with borrow: value and length of the result. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_sub_lemma"
  (words_as_type_indexed_bitvec)]
theorem mwSub_lemma {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)) (c : Bool) (zs : List (BitVec width)) (d : Bool),
      mwSub xs ys c = (zs, d) ∧ xs.length = ys.length →
      mw2n zs + mw2n ys + dimwords width xs.length * b2n d =
          mw2n xs + b2n c + (dimwords width xs.length - 1) ∧
        zs.length = xs.length := by
  intro xs
  induction xs with
  | nil =>
    rintro ys c zs d ⟨h, len⟩
    cases ys with
    | nil =>
      simp only [mwSub, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [mw2n, dimwords]
    | cons _ _ => simp at len
  | cons x xs ih =>
    rintro ys c zs d ⟨h, len⟩
    cases ys with
    | nil => simp at len
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [mwSub] at h
      rcases hz : singleSub x y c with ⟨z, c1⟩
      rcases hzs : mwSub xs ys c1 with ⟨zs', c2⟩
      simp only [hz, hzs, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have one := singleSub_thm x y z c c1 hz
      obtain ⟨val, lenEq⟩ := ih ys c1 zs' c2 ⟨hzs, len⟩
      refine ⟨?_, by simp [lenEq]⟩
      simp only [mw2n, List.length_cons, dimwords_succ]
      have pos : 0 < dimwords width xs.length := Nat.two_pow_pos _
      have hw : 0 < 2 ^ width := Nat.two_pow_pos _
      have key : 2 ^ width * (mw2n zs' + mw2n ys + dimwords width xs.length * b2n c2) =
          2 ^ width * (mw2n xs + b2n c1 + (dimwords width xs.length - 1)) := by rw [val]
      have e1 : 2 ^ width * (dimwords width xs.length - 1) =
          2 ^ width * dimwords width xs.length - 2 ^ width := by
        rw [Nat.mul_sub_one]
      have e2 : 2 ^ width ≤ 2 ^ width * dimwords width xs.length :=
        Nat.le_mul_of_pos_right _ pos
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add, e1, ← Nat.mul_assoc] at key
      omega

/-- Add with an optional final carry digit, padding the shorter second list. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_addv_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwAddv {width : Nat} [NeZero width] :
    List (BitVec width) → List (BitVec width) → Bool → List (BitVec width)
  | [], _, c => if c then [1] else []
  | x :: xs, ys, c =>
    let (y, ys2) := if ys = [] then ((0 : BitVec width), ys) else (holHd ys, ys.tail)
    let (z, c1) := singleAdd x y c
    z :: mwAddv xs ys2 c1

/-- Unequal-length addition splits into an equal-length addition and a
carry propagation over the zero-padded remainder. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_addv_EQ_mw_add"
  (words_as_type_indexed_bitvec)]
theorem mwAddv_EQ_mwAdd {width : Nat} [NeZero width] :
    ∀ (xs1 xs2 ys : List (BitVec width)) (c1 : Bool),
      ys.length = xs1.length →
      mwAddv (xs1 ++ xs2) ys c1 =
        let (zs1, c2) := mwAdd xs1 ys c1
        let (zs2, c3) := mwAdd xs2 (xs2.map (fun _ => (0 : BitVec width))) c2
        zs1 ++ zs2 ++ if c3 then [1] else [] := by
  intro xs1
  induction xs1 with
  | nil =>
    intro xs2 ys c1 len
    have ys0 : ys = [] := List.eq_nil_of_length_eq_zero len
    subst ys0
    simp only [mwAdd, List.nil_append]
    induction xs2 generalizing c1 with
    | nil => cases c1 <;> rfl
    | cons x xs2 ih2 =>
      simp only [mwAddv, if_true, List.map_cons, mwAdd, holHd, List.tail_cons]
      rw [ih2]
      rfl
  | cons x xs1 ih =>
    intro xs2 ys c1 len
    cases ys with
    | nil => simp at len
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [List.cons_append, mwAddv, List.cons_ne_nil, if_false, holHd, List.tail_cons,
        mwAdd]
      rw [ih xs2 ys _ len]
      rfl

/-- Subtraction of an appended first list continues the borrow into the suffix. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_sub_APPEND"
  (words_as_type_indexed_bitvec)]
theorem mwSub_APPEND {width : Nat} [NeZero width] :
    ∀ (xs1 xs2 ys : List (BitVec width)) (c : Bool),
      xs1.length = ys.length →
      mwSub (xs1 ++ xs2) ys c =
        let (ts1, c) := mwSub xs1 ys c
        let (ts2, c) := mwSub xs2 [] c
        (ts1 ++ ts2, c) := by
  intro xs1
  induction xs1 with
  | nil =>
    intro xs2 ys c len
    have ys0 : ys = [] := List.eq_nil_of_length_eq_zero len.symm
    subst ys0
    simp [mwSub]
  | cons x xs1 ih =>
    intro xs2 ys c len
    cases ys with
    | nil => simp at len
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [List.cons_append, mwSub]
      rw [ih xs2 ys _ len]

/-- Normalised subtraction. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_subv_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwSubv {width : Nat} [NeZero width] (xs ys : List (BitVec width)) :
    List (BitVec width) :=
  mwFix (mwSub xs ys true).1

private theorem mwSub_snoc_0 {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)) (c : Bool), mwSub xs (ys ++ [0]) c = mwSub xs ys c := by
  intro xs
  induction xs with
  | nil => intro ys c; simp [mwSub]
  | cons x xs ih =>
    intro ys c
    cases ys with
    | nil => simp only [List.nil_append, mwSub]
    | cons y ys => simp only [List.cons_append, mwSub, ih]

private theorem mwSub_append_0 {width : Nat} [NeZero width] :
    ∀ (n : Nat) (xs ys : List (BitVec width)) (c : Bool),
      mwSub xs (ys ++ List.replicate n 0) c = mwSub xs ys c := by
  intro n
  induction n with
  | zero => intro xs ys c; simp
  | succ n ih =>
    intro xs ys c
    rw [replicate_SNOC, ← List.append_assoc, mwSub_snoc_0, ih]

/-- Trailing zero digits of the subtrahend do not affect subtraction. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_sub_mw_fix"
  (words_as_type_indexed_bitvec)]
theorem mwSub_mwFix {width : Nat} [NeZero width] {c : Bool} :
    ∀ (xs ys : List (BitVec width)), mwSub xs (mwFix ys) c = mwSub xs ys c := by
  intro xs ys
  conv => rhs; rw [← mwFix_thm ys]
  rw [mwSub_append_0]

/-- Signed addition on sign-and-magnitude digit lists. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_add_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwiAdd {width : Nat} [NeZero width] :
    Bool × List (BitVec width) → Bool × List (BitVec width) → Bool × List (BitVec width)
  | (s, xs), (t, ys) =>
    if s = t then
      if ys.length ≤ xs.length then (s, mwAddv xs ys false) else (s, mwAddv ys xs false)
    else if mw2n ys = mw2n xs then (false, [])
    else if mw2n ys ≤ mw2n xs then (s, mwSubv xs ys) else (!s, mwSubv ys xs)

/-- Signed subtraction as addition of the negated second operand. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_sub_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwiSub {width : Nat} [NeZero width] :
    Bool × List (BitVec width) → Bool × List (BitVec width) → Bool × List (BitVec width)
  | (s, xs), (t, ys) => mwiAdd (s, xs) (!t, ys)

/-- `n2mw` is empty exactly at zero. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "n2mw_NIL"
  (words_as_type_indexed_bitvec)]
theorem n2mw_NIL {width : Nat} [NeZero width] :
    ∀ n : Nat, (n2mw n : List (BitVec width)) = [] ↔ n = 0 := by
  intro n
  rw [n2mw]
  split <;> simp_all

/-- One is a single digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "n2mw_1"
  (words_as_type_indexed_bitvec)]
theorem n2mw_1 {width : Nat} [NeZero width] : (n2mw 1 : List (BitVec width)) = [1] := by
  have hw : 1 < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  rw [n2mw, if_neg (by decide), Nat.mod_eq_of_lt hw, Nat.div_eq_of_lt hw,
    (n2mw_NIL 0).mpr rfl]
  rfl

theorem mwAddv_thm {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)) (c : Bool), ys.length ≤ xs.length →
      mw2n (mwAddv xs ys c) = mw2n xs + mw2n ys + b2n c := by
  intro xs
  induction xs with
  | nil =>
    intro ys c len
    have : ys = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp len)
    subst this
    have hw : 1 < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
    cases c <;> simp [mwAddv, mw2n, b2n, Nat.mod_eq_of_lt hw]
  | cons x xs ih =>
    intro ys c len
    cases ys with
    | nil =>
      simp only [mwAddv, if_true]
      rcases hz : singleAdd x 0 c with ⟨z, d⟩
      have one := singleAdd_thm x 0 z c d hz
      simp only [mw2n, ih [] d (Nat.zero_le _)] at one ⊢
      simp at one
      rw [Nat.mul_add, Nat.mul_add]; omega
    | cons y ys =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at len
      simp only [mwAddv, List.cons_ne_nil, if_false, holHd, List.tail_cons]
      rcases hz : singleAdd x y c with ⟨z, d⟩
      have one := singleAdd_thm x y z c d hz
      simp only [mw2n, ih ys d len]
      rw [Nat.mul_add, Nat.mul_add]; omega

theorem mwOk_addv {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)) (c : Bool), mwOk xs → mwOk ys → mwOk (mwAddv xs ys c) := by
  intro xs
  induction xs with
  | nil =>
    intro ys c _ _
    have hw : 1 < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
    cases c
    · simp [mwAddv, mwOk]
    · simp only [mwAddv, if_true]
      rw [mwOk_cons]
      refine ⟨fun _ h => ?_, by simp [mwOk]⟩
      have := congrArg BitVec.toNat h
      simp [Nat.mod_eq_of_lt hw] at this
  | cons x xs ih =>
    intro ys c okx oky
    rw [mwOk_cons] at okx
    have oky2 : mwOk (if ys = [] then ((0 : BitVec width), ys) else (holHd ys, ys.tail)).2 := by
      cases ys with
      | nil => simpa using oky
      | cons y ys => simpa using ((mwOk_cons y ys).mp oky).2
    simp only [mwAddv]
    rcases hp : (if ys = [] then ((0 : BitVec width), ys) else (holHd ys, ys.tail)) with ⟨y, ys2⟩
    rw [hp] at oky2
    rcases hz : singleAdd x y c with ⟨z, d⟩
    simp only
    rw [mwOk_cons]
    refine ⟨fun empty => ?_, ih ys2 d okx.2 oky2⟩
    cases xs with
    | cons _ _ => cases d <;> simp [mwAddv] at empty
    | nil =>
      have xnz := okx.1 rfl
      cases d
      · intro zz
        subst zz
        have one := singleAdd_thm x y 0 c false hz
        have : x.toNat ≠ 0 := fun e => xnz (BitVec.eq_of_toNat_eq (by simpa using e))
        simp [b2n] at one; omega
      · simp [mwAddv] at empty

private theorem mwAddv_ne_nil {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)) (c : Bool), mwAddv xs ys c = [] → xs = [] := by
  intro xs ys c h
  cases xs with
  | nil => rfl
  | cons x xs => simp [mwAddv] at h

theorem mwSub_thm {width : Nat} [NeZero width] (xs ys : List (BitVec width))
    (len : xs.length = ys.length) (le : mw2n ys ≤ mw2n xs) :
    mw2n (mwSub xs ys true).1 = mw2n xs - mw2n ys := by
  rcases h : mwSub xs ys true with ⟨zs, d⟩
  obtain ⟨val, zlen⟩ := mwSub_lemma xs ys true zs d ⟨h, len⟩
  have pos : 0 < dimwords width xs.length := Nat.two_pow_pos _
  have lz := mw2n_lt zs
  have ly := mw2n_lt ys
  rw [zlen] at lz
  rw [← len] at ly
  cases d <;> simp only [b2n] at val <;> simp only <;> omega

private theorem mw2n_append_replicate {width : Nat} [NeZero width] (ys : List (BitVec width)) (n : Nat) :
    mw2n (ys ++ List.replicate n 0) = mw2n ys := by
  rw [mw2n_append]
  have gen : ∀ (m : Nat) (z : BitVec width), z.toNat = 0 → mw2n (List.replicate m z) = 0 := by
    intro m z hz
    induction m with
    | zero => rfl
    | succ m ih => simp only [List.replicate_succ, mw2n, hz, ih, Nat.mul_zero]
  rw [gen n _ (by simp), Nat.mul_zero, Nat.add_zero]

theorem mwSubv_thm {width : Nat} [NeZero width] (xs ys : List (BitVec width))
    (le : mw2n ys ≤ mw2n xs) (len : ys.length ≤ xs.length) :
    mw2n (mwSubv xs ys) = mw2n xs - mw2n ys := by
  simp only [mwSubv]
  rw [mw2n_mwFix, ← mwSub_append_0 (xs.length - ys.length)]
  rw [mwSub_thm xs _ (by simp; omega) (by rw [mw2n_append_replicate]; exact le),
    mw2n_append_replicate]

theorem mwOk_eq_n2mw {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width), mwOk xs → xs = n2mw (mw2n xs) := by
  intro xs
  induction xs with
  | nil => intro _; simp [mw2n, n2mw]
  | cons x xs ih =>
    intro ok
    rw [mwOk_cons] at ok
    have hx := x.isLt
    have hw : 0 < 2 ^ width := Nat.two_pow_pos _
    have tail := ih ok.2
    have nz : mw2n (x :: xs) ≠ 0 := by
      simp only [mw2n]
      cases xs with
      | nil =>
        have : x.toNat ≠ 0 := fun e => ok.1 rfl (BitVec.eq_of_toNat_eq (by simpa using e))
        omega
      | cons y ys =>
        have : mw2n (y :: ys) ≠ 0 := fun e =>
          List.cons_ne_nil y ys ((mwOk_mwFix_ID _ ok.2).symm.trans ((mwFix_NIL _).mpr e))
        have : 0 < 2 ^ width * mw2n (y :: ys) := Nat.mul_pos hw (Nat.pos_of_ne_zero this)
        omega
    rw [n2mw, if_neg nz]
    simp only [mw2n]
    have m : (x.toNat + 2 ^ width * mw2n xs) % 2 ^ width = x.toNat := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    have d : (x.toNat + 2 ^ width * mw2n xs) / 2 ^ width = mw2n xs := by
      rw [Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hx, Nat.zero_add]
    rw [m, d, ← tail]
    simp

private theorem canonical_eq_i2mw {width : Nat} [NeZero width] (s : Bool) (xs : List (BitVec width))
    (ok : mwOk xs) (notNegZero : (s, xs) ≠ (true, [])) :
    (s, xs) = i2mw (mw2i (s, xs)) := by
  have hx := mwOk_eq_n2mw xs ok
  cases s
  · simp only [mw2i, i2mw]
    rw [hx]; simp [mw2n_n2mw]
  · have ne : xs ≠ [] := fun h => notNegZero (by rw [h])
    have pos : mw2n xs ≠ 0 := fun e => ne ((mwOk_mwFix_ID _ ok).symm.trans ((mwFix_NIL _).mpr e))
    simp only [mw2i, i2mw]
    rw [hx]; simp [mw2n_n2mw]; omega

private theorem mwiAdd_lemma {width : Nat} [NeZero width] (s t : Bool) (xs ys : List (BitVec width))
    (okx : mwOk xs) (oky : mwOk ys) :
    mw2i (mwiAdd (s, xs) (t, ys)) = mw2i (s, xs) + mw2i (t, ys) := by
  simp only [mwiAdd]
  by_cases st : s = t
  · subst st
    by_cases len : ys.length ≤ xs.length
    · simp only [if_true, len]
      cases s <;> simp [mw2i, mwAddv_thm _ _ _ len, b2n] <;> omega
    · simp only [if_true, len, if_false]
      have len' : xs.length ≤ ys.length := by omega
      cases s <;> simp [mw2i, mwAddv_thm _ _ _ len', b2n] <;> omega
  · simp only [st, if_false]
    by_cases eq : mw2n ys = mw2n xs
    · simp only [eq, if_true]
      cases s <;> cases t <;> simp_all [mw2i, mw2n] <;> omega
    · simp only [eq, if_false]
      by_cases le : mw2n ys ≤ mw2n xs
      · have len := mw2n_LESS ys xs ⟨oky, okx, le⟩
        simp only [le, if_true]
        cases s <;> cases t <;> simp_all [mw2i, mwSubv_thm xs ys le len] <;> omega
      · have le' : mw2n xs ≤ mw2n ys := by omega
        have len := mw2n_LESS xs ys ⟨okx, oky, le'⟩
        simp only [le, if_false]
        cases s <;> cases t <;> simp_all [mw2i, mwSubv_thm ys xs le' len] <;> omega

private theorem mwiAdd_canonical {width : Nat} [NeZero width] (s t : Bool)
    (xs ys : List (BitVec width)) (okx : mwOk xs) (oky : mwOk ys)
    (notNegZero : (s, xs) ≠ (true, [])) :
    mwOk (mwiAdd (s, xs) (t, ys)).2 ∧ mwiAdd (s, xs) (t, ys) ≠ (true, []) := by
  simp only [mwiAdd]
  by_cases st : s = t
  · simp only [st, if_true]
    by_cases len : ys.length ≤ xs.length
    · simp only [len, if_true]
      refine ⟨mwOk_addv _ _ _ okx oky, ?_⟩
      intro h
      simp only [Prod.mk.injEq] at h
      exact notNegZero (by rw [st, h.1, mwAddv_ne_nil _ _ _ h.2])
    · simp only [len, if_false]
      refine ⟨mwOk_addv _ _ _ oky okx, ?_⟩
      intro h
      simp only [Prod.mk.injEq] at h
      have ys0 := mwAddv_ne_nil _ _ _ h.2
      rw [ys0] at len
      simp at len
  · simp only [st, if_false]
    by_cases eq : mw2n ys = mw2n xs
    · simp only [eq, if_true]; exact ⟨by simp [mwOk], by simp⟩
    · simp only [eq, if_false]
      split
      · rename_i le
        refine ⟨mwOk_fix _, ?_⟩
        intro h
        simp only [Prod.mk.injEq] at h
        have len := mw2n_LESS _ _ ⟨oky, okx, le⟩
        have v := mwSubv_thm _ _ le len
        rw [h.2] at v
        simp [mw2n] at v; omega
      · rename_i le
        refine ⟨mwOk_fix _, ?_⟩
        intro h
        simp only [Prod.mk.injEq] at h
        have le' : mw2n xs ≤ mw2n ys := by omega
        have len := mw2n_LESS _ _ ⟨okx, oky, le'⟩
        have v := mwSubv_thm _ _ le' len
        rw [h.2] at v
        simp [mw2n] at v; omega

private theorem i2mw_notNegZero {width : Nat} [NeZero width] (i : Int) :
    (i2mw i : Bool × List (BitVec width)) ≠ (true, []) := by
  simp only [i2mw, ne_eq, Prod.mk.injEq, decide_eq_true_eq, n2mw_NIL, Int.natAbs_eq_zero]
  omega

private theorem mwiAdd_i2mw {width : Nat} [NeZero width] (i : Int) (t : Bool)
    (ys : List (BitVec width)) (oky : mwOk ys) :
    mwiAdd (i2mw i) (t, ys) = i2mw (i + mw2i (t, ys)) := by
  rcases hx : (i2mw i : Bool × List (BitVec width)) with ⟨s, xs⟩
  have okx : mwOk xs := mwOk_i2mw i s xs hx
  have nnz : (s, xs) ≠ (true, []) := hx ▸ i2mw_notNegZero i
  obtain ⟨ok, nz⟩ := mwiAdd_canonical s t xs ys okx oky nnz
  rcases h : mwiAdd (s, xs) (t, ys) with ⟨r, zs⟩
  rw [h] at ok nz
  rw [canonical_eq_i2mw r zs ok nz, ← h, mwiAdd_lemma _ _ _ _ okx oky, ← hx, mw2i_i2mw]

/-- Signed multiword addition implements integer addition. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_add_thm"
  (words_as_type_indexed_bitvec)]
theorem mwiAdd_thm {width : Nat} [NeZero width] :
    ∀ (i j : Int), mwiAdd (i2mw i : Bool × List (BitVec width)) (i2mw j) = i2mw (i + j) := by
  intro i j
  have := mwiAdd_i2mw (width := width) i (i2mw j : Bool × List (BitVec width)).1
    (i2mw j : Bool × List (BitVec width)).2 (mwOk_n2mw _)
  rw [this, mw2i_i2mw]

/-- Signed multiword subtraction implements integer subtraction. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_sub_thm"
  (words_as_type_indexed_bitvec)]
theorem mwiSub_thm {width : Nat} [NeZero width] :
    ∀ (i j : Int), mwiSub (i2mw i : Bool × List (BitVec width)) (i2mw j) = i2mw (i - j) := by
  intro i j
  rcases hy : (i2mw j : Bool × List (BitVec width)) with ⟨t, ys⟩
  have oky : mwOk ys := mwOk_i2mw j t ys hy
  simp only [mwiSub]
  rw [mwiAdd_i2mw i (!t) ys oky]
  have : mw2i ((!t), ys) = -mw2i (t, ys) := by cases t <;> simp [mw2i]
  rw [this, ← hy, mw2i_i2mw, Int.sub_eq_add_neg]

end Flapjack.Misc.Multiword
