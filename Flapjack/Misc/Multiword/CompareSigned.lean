module

public import Flapjack.Misc.Multiword.Compare
public import Flapjack.Misc.Multiword.AddSub
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Unsigned and signed comparison of multiword numbers. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Compare digit lists, first by length, then digit by digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_compare_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwCompare {width : Nat} [NeZero width] (xs ys : List (BitVec width)) :
    Option Bool :=
  if xs.length < ys.length then some (decide ((0 : Nat) < 1))
  else if ys.length < xs.length then some (decide ((1 : Nat) < 0))
  else mwCmp xs ys

open Classical in
/-- Map a comparison outcome to inequality with `b`; the element type is arbitrary. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "option_eq_def"]
noncomputable def optionEq {α : Type} (b : α) : Option α → Option Bool
  | none => none
  | some x => some (decide (b ≠ x))

/-- Signed comparison: equal signs compare magnitudes, adjusted by the sign. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_compare_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwiCompare {width : Nat} [NeZero width] :
    Bool × List (BitVec width) → Bool × List (BitVec width) → Option Bool
  | (s, xs), (t, ys) => if s = t then optionEq s (mwCompare xs ys) else some s

/-- Signed less-than. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_lt_def"
  (words_as_type_indexed_bitvec)]
def mwiLt {width : Nat} [NeZero width] (s_xs t_ys : Bool × List (BitVec width)) : Prop :=
  mwiCompare s_xs t_ys = some true

/-- Signed equality. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_eq_def"
  (words_as_type_indexed_bitvec)]
def mwiEq {width : Nat} [NeZero width] (s_xs t_ys : Bool × List (BitVec width)) : Prop :=
  mwiCompare s_xs t_ys = none

/-- A well-formed number with fewer digits is smaller. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_LESS_IMP_mw2n_LESS"
  (words_as_type_indexed_bitvec)]
theorem length_less_imp_mw2n_less {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)), mwOk xs ∧ mwOk ys ∧ xs.length < ys.length →
      mw2n xs < mw2n ys := by
  rintro xs ys ⟨_, oky, len⟩
  have ne : ys ≠ [] := by intro h; simp [h] at len
  have hy := mw2n_gt ys oky ne
  have hx := mw2n_lt xs
  have : dimwords width xs.length ≤ dimwords width (ys.length - 1) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  omega

/-- For well-formed numbers, a smaller value has no more digits. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw2n_LESS_IMP_LENGTH_LESS_EQ"
  (words_as_type_indexed_bitvec)]
theorem mw2n_less_imp_length_le {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)), mwOk xs ∧ mwOk ys ∧ mw2n xs < mw2n ys →
      xs.length ≤ ys.length := by
  rintro xs ys ⟨okx, oky, lt⟩
  exact Nat.le_of_not_lt fun h => by
    have := length_less_imp_mw2n_less ys xs ⟨oky, okx, h⟩
    omega

/-- Comparison of well-formed numbers decides the order of their values. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_compare_thm"
  (words_as_type_indexed_bitvec)]
theorem mwCompare_thm {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)), mwOk xs ∧ mwOk ys →
      mwCompare xs ys = if mw2n xs = mw2n ys then none else some (decide (mw2n xs < mw2n ys)) := by
  rintro xs ys ⟨okx, oky⟩
  simp only [mwCompare]
  by_cases l1 : xs.length < ys.length
  · have := length_less_imp_mw2n_less xs ys ⟨okx, oky, l1⟩
    simp [l1, Nat.ne_of_lt this, this]
  · by_cases l2 : ys.length < xs.length
    · have := length_less_imp_mw2n_less ys xs ⟨oky, okx, l2⟩
      simp [l1, l2, Nat.ne_of_gt this, Nat.not_lt_of_gt this]
    · simp only [l1, l2, if_false]
      exact mwCmpThm xs ys (by omega)

/-- Signed comparison of `i2mw` numbers decides the integer order. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mwi_compare_thm"
  (words_as_type_indexed_bitvec)]
theorem mwiCompare_thm {width : Nat} [NeZero width] :
    ∀ (i j : Int), mwiCompare (i2mw i : Bool × List (BitVec width)) (i2mw j) =
      if i = j then none else some (decide (i < j)) := by
  intro i j
  simp only [i2mw, mwiCompare, mwCompare_thm _ _ ⟨mwOk_n2mw _, mwOk_n2mw _⟩, mw2n_n2mw]
  by_cases hi : i < 0 <;> by_cases hj : j < 0
  · simp only [hi, hj, decide_true, if_true]
    by_cases e : i.natAbs = j.natAbs
    · simp [optionEq, show i = j by omega]
    · simp [e, optionEq, show i ≠ j by omega]; omega
  · simp [hi, hj, show i ≠ j by omega, show i < j by omega]
  · simp [hi, hj, show i ≠ j by omega, show ¬ i < j by omega]
  · simp only [hi, hj, decide_false, if_true]
    by_cases e : i.natAbs = j.natAbs
    · simp [optionEq, show i = j by omega]
    · simp [e, optionEq, show i ≠ j by omega]; omega

/-- Subtracting a strictly smaller well-formed number leaves a nonempty result. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_subv_NOT_NIL"
  (words_as_type_indexed_bitvec)]
theorem mwSubv_NOT_NIL {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)), mwOk xs ∧ mwOk ys ∧ mw2n xs < mw2n ys →
      mwSubv ys xs ≠ [] := by
  rintro xs ys ⟨okx, oky, lt⟩ h
  have len := mw2n_less_imp_length_le xs ys ⟨okx, oky, lt⟩
  have v := mwSubv_thm ys xs (Nat.le_of_lt lt) len
  rw [h] at v
  simp [mw2n] at v
  omega

/-- Least-significant-first comparison carrying the outcome of the lower digits. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_cmp_alt_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwCmpAlt {width : Nat} [NeZero width] :
    List (BitVec width) → List (BitVec width) → Option Bool → Option Bool
  | [], _, b => b
  | x :: xs, ys, b =>
    mwCmpAlt xs ys.tail
      (if x = holHd ys then b else if x < holHd ys then some true else some false)

private theorem mwCmpAlt_value {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)) (res : Option Bool), xs.length = ys.length →
      mwCmpAlt xs ys res =
        if mw2n xs = mw2n ys then res else some (decide (mw2n xs < mw2n ys)) := by
  intro xs
  induction xs with
  | nil =>
    intro ys res len
    have : ys = [] := List.eq_nil_of_length_eq_zero len.symm
    subst this
    simp [mwCmpAlt, mw2n]
  | cons x xs ih =>
    intro ys res len
    cases ys with
    | nil => simp at len
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [mwCmpAlt, holHd, List.tail_cons, mw2n]
      rw [ih ys _ len]
      have hx := x.isLt
      have hy := y.isLt
      have hw : 0 < 2 ^ width := Nat.two_pow_pos _
      by_cases e : mw2n xs = mw2n ys
      · simp only [e, if_true, Nat.add_right_cancel_iff, Nat.add_lt_add_iff_right]
        by_cases xy : x = y
        · subst xy; simp
        · have tn : x.toNat ≠ y.toNat := fun h => xy (BitVec.eq_of_toNat_eq h)
          by_cases l : x.toNat < y.toNat <;> simp [xy, tn, BitVec.lt_def, l]
      · simp only [e, if_false]
        rcases Nat.lt_or_gt_of_ne e with l | l
        · have : 2 ^ width * mw2n xs + 2 ^ width ≤ 2 ^ width * mw2n ys := by
            rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ l
          have : x.toNat + 2 ^ width * mw2n xs < y.toNat + 2 ^ width * mw2n ys := by omega
          simp [l, this, Nat.ne_of_lt this]
        · have : 2 ^ width * mw2n ys + 2 ^ width ≤ 2 ^ width * mw2n xs := by
            rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ l
          have : y.toNat + 2 ^ width * mw2n ys < x.toNat + 2 ^ width * mw2n xs := by omega
          simp [Nat.not_lt_of_gt l, Nat.not_lt_of_gt this, Nat.ne_of_gt this]

/-- On equal lengths, the alternative comparison agrees with `mw_cmp`. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_cmp_alt_thm"
  (words_as_type_indexed_bitvec)]
theorem mwCmp_alt_thm {width : Nat} [NeZero width] {xs ys : List (BitVec width)} :
    xs.length = ys.length → mwCmp xs ys = mwCmpAlt xs ys none := by
  intro len
  rw [mwCmpThm xs ys len.symm, mwCmpAlt_value xs ys none len]

end Flapjack.Misc.Multiword
