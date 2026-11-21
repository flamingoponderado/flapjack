module

public import Flapjack.Misc.Multiword

@[expose] public section

/-! Fixed-length word digit lists and well-formed multiword numbers. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- The modulus of `k` words of the given width. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "dimwords_def"
  (word_dimension_as_width := width)]
def dimwords (width : Nat) [NeZero width] (k : Nat) : Nat := 2 ^ (k * width)

/-- The `k` least significant word digits of `n`. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "k2mw_def"
  (words_as_type_indexed_bitvec)]
def k2mw {width : Nat} [NeZero width] : Nat → Nat → List (BitVec width)
  | 0, _ => []
  | l + 1, n => BitVec.ofNat width n :: k2mw l (n / 2 ^ width)

/-- A digit list is well formed when it has no most-significant zero word. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_ok_def"
  (words_as_type_indexed_bitvec)]
def mwOk {width : Nat} [NeZero width] (xs : List (BitVec width)) : Prop :=
  xs ≠ [] → holLast xs ≠ 0

theorem dimwords_succ {width : Nat} [NeZero width] (k : Nat) :
    dimwords width (k + 1) = 2 ^ width * dimwords width k := by
  simp only [dimwords, Nat.succ_mul, Nat.pow_add, Nat.mul_comm]

theorem dimwords_pos {width : Nat} [NeZero width] (k : Nat) : 0 < dimwords width k :=
  Nat.two_pow_pos _

/-- Appending the next digit computes one more word of the number. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "k2mw_SNOC"
  (words_as_type_indexed_bitvec)]
theorem k2mw_SNOC {width : Nat} [NeZero width] :
    ∀ (k n : Nat), (k2mw (k + 1) n : List (BitVec width)) =
      k2mw k n ++ [BitVec.ofNat width (n / dimwords width k)] := by
  intro k
  induction k with
  | zero => intro n; simp [k2mw, dimwords]
  | succ k ih =>
    intro n
    rw [k2mw, ih, k2mw]
    simp only [List.cons_append, Nat.div_div_eq_div_mul, dimwords_succ]

/-- `k2mw k` always produces `k` words. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_k2mw"
  (words_as_type_indexed_bitvec)]
theorem length_k2mw {width : Nat} [NeZero width] :
    ∀ (k n : Nat), (k2mw k n : List (BitVec width)).length = k := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih => intro n; simp [k2mw, ih]

/-- The value of appended digit lists. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw2n_APPEND"
  (words_as_type_indexed_bitvec)]
theorem mw2n_append {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)),
      mw2n (xs ++ ys) = mw2n xs + dimwords width xs.length * mw2n ys := by
  intro xs
  induction xs with
  | nil => intro ys; simp [mw2n, dimwords]
  | cons x xs ih =>
    intro ys
    simp only [List.cons_append, mw2n, ih, List.length_cons, dimwords_succ]
    rw [Nat.mul_add, Nat.mul_assoc]
    omega

theorem mw2n_lt {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width), mw2n xs < dimwords width xs.length := by
  intro xs
  induction xs with
  | nil => simp [mw2n, dimwords]
  | cons x xs ih =>
    simp only [mw2n, List.length_cons, dimwords_succ]
    have hx := x.isLt
    have : x.toNat + 2 ^ width * mw2n xs < 2 ^ width * (mw2n xs + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_left _ ih)

/-- Every digit list is the fixed-length expansion of a number in range. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "k2mw_EXISTS"
  (words_as_type_indexed_bitvec)]
theorem k2mw_EXISTS {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width), ∃ k, xs = k2mw xs.length k ∧ k < dimwords width xs.length := by
  intro xs
  refine ⟨mw2n xs, ?_, mw2n_lt xs⟩
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, k2mw, mw2n]
    have hx := x.isLt
    have lo : BitVec.ofNat width (x.toNat + 2 ^ width * mw2n xs) = x := by
      apply BitVec.eq_of_toNat_eq
      simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    have hi : (x.toNat + 2 ^ width * mw2n xs) / 2 ^ width = mw2n xs := by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos width), Nat.div_eq_of_lt hx, Nat.zero_add]
    rw [lo, hi, ← ih]

theorem mwOk_cons {width : Nat} [NeZero width] (x : BitVec width)
    (xs : List (BitVec width)) :
    mwOk (x :: xs) ↔ (xs = [] → x ≠ 0) ∧ mwOk xs := by
  cases xs with
  | nil => simp [mwOk, holLast]
  | cons y ys => simp [mwOk, holLast_cons]

theorem mw2n_gt {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width), mwOk xs → xs ≠ [] → dimwords width (xs.length - 1) ≤ mw2n xs := by
  intro xs
  induction xs with
  | nil => intro _ h; exact absurd rfl h
  | cons x xs ih =>
    intro ok _
    rw [mwOk_cons] at ok
    cases xs with
    | nil =>
      have : x ≠ 0 := ok.1 rfl
      have : x.toNat ≠ 0 := fun h => this (BitVec.eq_of_toNat_eq (by simpa using h))
      simp [mw2n, dimwords]; omega
    | cons y ys =>
      have h := ih ok.2 (List.cons_ne_nil _ _)
      simp only [List.length_cons] at h ⊢
      rw [show ys.length + 1 + 1 - 1 = ys.length + 1 by omega, dimwords_succ]
      rw [show ys.length + 1 - 1 = ys.length by omega] at h
      show _ ≤ x.toNat + 2 ^ width * mw2n (y :: ys)
      have := Nat.mul_le_mul_left (2 ^ width) h
      omega

/-- For well-formed numbers, a smaller value has no more digits. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw2n_LESS"
  (words_as_type_indexed_bitvec)]
theorem mw2n_LESS {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)),
      mwOk xs ∧ mwOk ys ∧ mw2n xs ≤ mw2n ys → xs.length ≤ ys.length := by
  rintro xs ys ⟨okx, oky, le⟩
  by_cases ex : xs = []
  · simp [ex]
  have gx := mw2n_gt xs okx ex
  have ly := mw2n_lt ys
  have lt : dimwords width (xs.length - 1) < dimwords width ys.length := by omega
  simp only [dimwords] at lt
  have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp lt
  have : xs.length - 1 < ys.length := Nat.lt_of_mul_lt_mul_right this
  have : xs.length ≠ 0 := fun h => ex (List.eq_nil_of_length_eq_zero h)
  omega

/-- `n2mw` produces well-formed digit lists. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_ok_n2mw"
  (words_as_type_indexed_bitvec)]
theorem mwOk_n2mw {width : Nat} [NeZero width] (n : Nat) : mwOk (n2mw n : List (BitVec width)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [n2mw]
    split
    · simp [mwOk]
    · rename_i nz
      rw [mwOk_cons]
      have pos := Nat.two_pow_pos width
      refine ⟨?_, ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero nz) (Nat.one_lt_two_pow (NeZero.ne width)))⟩
      intro tail zero
      have small : n / 2 ^ width = 0 := Classical.byContradiction fun h => by
        rw [n2mw, if_neg h] at tail
        exact List.cons_ne_nil _ _ tail
      have lt : n < 2 ^ width := (Nat.div_eq_zero_iff_lt pos).mp small
      have := congrArg BitVec.toNat zero
      simp [Nat.mod_eq_of_lt lt] at this
      exact nz this

/-- The digits of every `i2mw` result are well formed. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_ok_i2mw"
  (words_as_type_indexed_bitvec)]
theorem mwOk_i2mw {width : Nat} [NeZero width] :
    ∀ (i : Int) (x : Bool) (xs : List (BitVec width)), i2mw i = (x, xs) → mwOk xs := by
  intro i x xs h
  simp only [i2mw, Prod.mk.injEq] at h
  rw [← h.2]
  exact mwOk_n2mw _

/-- `n2mw` is injective. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "n2mw_11"
  (words_as_type_indexed_bitvec)]
theorem n2mw_11 {width : Nat} [NeZero width] :
    ∀ (m n : Nat), (n2mw m : List (BitVec width)) = n2mw n ↔ m = n := by
  intro m n
  constructor
  · intro h
    have := congrArg mw2n h
    rwa [mw2n_n2mw, mw2n_n2mw] at this
  · intro h; rw [h]

/-- `i2mw` is injective. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "i2mw_11"
  (words_as_type_indexed_bitvec)]
theorem i2mw_11 {width : Nat} [NeZero width] :
    ∀ (i j : Int), (i2mw i : Bool × List (BitVec width)) = i2mw j ↔ i = j := by
  intro i j
  constructor
  · intro h
    have := congrArg mw2i h
    rwa [mw2i_i2mw, mw2i_i2mw] at this
  · intro h; rw [h]

/-- Drop most-significant zero words. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_fix_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwFix {width : Nat} [NeZero width] (xs : List (BitVec width)) :
    List (BitVec width) :=
  if xs = [] then [] else if holLast xs = 0 then mwFix xs.dropLast else xs
termination_by xs.length
decreasing_by
  simp only [List.length_dropLast]
  cases xs <;> simp_all

/-- Normalise negative zero to positive zero. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_zerofix_def"]
def mwZerofix {α : Type} (x : Bool × List α) : Bool × List α :=
  match x with
  | (true, []) => (false, [])
  | _ => x

theorem holLast_append_singleton {α : Type} [Nonempty α] (xs : List α) (y : α) :
    holLast (xs ++ [y]) = y := by
  induction xs with
  | nil => simp [holLast]
  | cons x xs ih =>
    rw [List.cons_append, holLast_cons, if_neg (by simp), ih]

theorem snoc_induction {α : Type} {motive : List α → Prop} (nil : motive [])
    (snoc : ∀ xs y, motive xs → motive (xs ++ [y])) : ∀ xs, motive xs := by
  intro xs
  rw [← List.reverse_reverse xs]
  induction xs.reverse with
  | nil => exact nil
  | cons y ys ih => rw [List.reverse_cons]; exact snoc _ y ih

theorem mwFix_snoc {width : Nat} [NeZero width] (xs : List (BitVec width)) (y : BitVec width) :
    mwFix (xs ++ [y]) = if y = 0 then mwFix xs else xs ++ [y] := by
  rw [mwFix, if_neg (by simp), holLast_append_singleton, List.dropLast_concat]

theorem mwOk_snoc {width : Nat} [NeZero width] (xs : List (BitVec width)) (y : BitVec width) :
    mwOk (xs ++ [y]) ↔ y ≠ 0 := by
  simp [mwOk, holLast_append_singleton]

/-- `mw_fix` always yields a well-formed list. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_ok_fix"
  (words_as_type_indexed_bitvec)]
theorem mwOk_fix {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width), mwOk (mwFix xs) := by
  intro xs
  induction xs using snoc_induction with
  | nil => simp [mwFix, mwOk]
  | snoc xs y ih =>
    rw [mwFix_snoc]
    split
    · exact ih
    · rename_i h; exact (mwOk_snoc xs y).mpr h

/-- `mw_fix` leaves well-formed lists unchanged. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_ok_mw_fix_ID"
  (words_as_type_indexed_bitvec)]
theorem mwOk_mwFix_ID {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width), mwOk xs → mwFix xs = xs := by
  intro xs ok
  cases xs.eq_nil_or_concat with
  | inl h => subst h; simp [mwFix]
  | inr h =>
    obtain ⟨ys, y, rfl⟩ := h
    rw [List.concat_eq_append] at ok ⊢
    rw [mwFix_snoc, if_neg ((mwOk_snoc ys y).mp ok)]

theorem mw2n_mwFix {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width), mw2n (mwFix xs) = mw2n xs := by
  intro xs
  induction xs using snoc_induction with
  | nil => simp [mwFix]
  | snoc xs y ih =>
    rw [mwFix_snoc]
    split
    · rename_i h; subst h; rw [ih, mw2n_append]; simp [mw2n]
    · rfl

/-- `mw_fix` is empty exactly for the value zero. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_fix_NIL" 438
  (words_as_type_indexed_bitvec)]
theorem mwFix_NIL {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width), mwFix xs = [] ↔ mw2n xs = 0 := by
  intro xs
  induction xs using snoc_induction with
  | nil => simp [mwFix, mw2n]
  | snoc xs y ih =>
    rw [mwFix_snoc, mw2n_append]
    have pos := dimwords_pos (width := width) xs.length
    split
    · rename_i h; subst h; simp [mw2n, ih]
    · rename_i h
      have : y.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
      simp only [mw2n]
      constructor
      · intro e; simp at e
      · intro e
        have : dimwords width xs.length * (y.toNat + 2 ^ width * 0) = 0 := by omega
        rcases Nat.mul_eq_zero.mp this with z | z <;> omega

/-- `mw_fix` never lengthens a list. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_mw_fix"
  (words_as_type_indexed_bitvec)]
theorem length_mwFix {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width), (mwFix xs).length ≤ xs.length := by
  intro xs
  induction xs using snoc_induction with
  | nil => simp [mwFix]
  | snoc xs y ih =>
    rw [mwFix_snoc]
    split
    · simp; omega
    · exact Nat.le_refl _

/-- Replicating one more element appends it at the end. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "REPLICATE_SNOC"]
theorem replicate_SNOC {α : Type} :
    ∀ (n : Nat) (x : α), List.replicate (n + 1) x = List.replicate n x ++ [x] := by
  intro n x
  exact List.replicate_succ' ..

/-- `mw_fix` removed exactly a suffix of zero words. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_fix_thm"
  (words_as_type_indexed_bitvec)]
theorem mwFix_thm {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width),
      mwFix xs ++ List.replicate (xs.length - (mwFix xs).length) 0 = xs := by
  intro xs
  induction xs using snoc_induction with
  | nil => simp [mwFix]
  | snoc xs y ih =>
    rw [mwFix_snoc]
    split
    · rename_i h; subst h
      have le := length_mwFix xs
      rw [List.length_append, List.length_singleton,
        show xs.length + 1 - (mwFix xs).length = (xs.length - (mwFix xs).length) + 1 by omega,
        replicate_SNOC, ← List.append_assoc, ih]
    · simp

end Flapjack.Misc.Multiword
