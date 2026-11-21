module

public import Flapjack.Misc.Multiword.Mul

@[expose] public section

/-! General definitions and arithmetic lemmas of the multiword division section. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Multiply a digit list by a single word. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_mul_by_single_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwMulBySingle {width : Nat} [NeZero width] (x : BitVec width)
    (ys : List (BitVec width)) : List (BitVec width) :=
  mwMulPass x ys (k2mw ys.length 0) 0

/-- A multiplication pass produces one more digit than its multiplicand. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_mw_mul_pass"
  (words_as_type_indexed_bitvec)]
theorem length_mwMulPass {width : Nat} [NeZero width] :
    ∀ (ys zs : List (BitVec width)) (x k : BitVec width),
      (mwMulPass x ys zs k).length = ys.length + 1 := by
  intro ys
  induction ys with
  | nil => intro zs x k; rfl
  | cons y ys ih =>
    intro zs x k
    simp only [mwMulPass, List.length_cons]
    rw [ih]

/-- Multiplication by a single word produces one more digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_mw_mul_by_single"
  (words_as_type_indexed_bitvec)]
theorem length_mwMulBySingle {width : Nat} [NeZero width] {x : BitVec width}
    {ys : List (BitVec width)} : (mwMulBySingle x ys).length = ys.length + 1 :=
  length_mwMulPass _ _ _ _

/-- Cancel a dominated summand from a strict sum inequality. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "EQ_A_S_R_2"]
theorem EQ_A_S_R_2 : ∀ (c d a b : Nat), d ≤ c ∧ a + c < b + d → a < b := by
  intro c d a b ⟨h1, h2⟩
  omega

/-- Dividing by a larger divisor gives a smaller quotient. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "DIV_thm1"]
theorem DIV_thm1 {a b c : Nat} : 0 < b ∧ b ≤ c → a / c ≤ a / b := by
  intro ⟨hb, hbc⟩
  exact Nat.div_le_div_left hbc hb

/-- A quotient below a bound. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "DIV_thm2"]
theorem DIV_thm2 {a b c : Nat} : 0 < b ∧ a < c * b → a / b < c := by
  intro ⟨hb, h⟩
  exact (Nat.div_lt_iff_lt_mul hb).mpr h

/-- The quotient times the divisor does not exceed the dividend. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "DIV_thm3"]
theorem DIV_thm3 : ∀ (a b : Nat), 0 < b → a / b * b ≤ a := by
  intro a b _
  exact Nat.div_mul_le_self a b

/-- The remainder is below the divisor. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "DIV_thm4"]
theorem DIV_thm4 : ∀ (a b : Nat), 0 < b → a - a / b * b < b := by
  intro a b hb
  rw [Nat.mul_comm (a / b) b]
  have := Nat.div_add_mod a b
  have := Nat.mod_lt a hb
  omega

/-- The dividend is below the next multiple of the divisor. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "DIV_thm4_bis"]
theorem DIV_thm4_bis : ∀ (a b : Nat), 0 < b → a < b + a / b * b := by
  intro a b hb
  rw [Nat.mul_comm (a / b) b]
  have := Nat.div_add_mod a b
  have := Nat.mod_lt a hb
  omega

/-- A candidate quotient with a remainder below the divisor is at least the quotient. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "DIV_thm5"]
theorem DIV_thm5 {a b q : Nat} : 0 < b ∧ a - q * b < b → q ≥ a / b := by
  intro ⟨hb, h⟩
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul hb, Nat.succ_mul]
  omega

/-- A nonzero word has a positive value. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "NOT_0w_bis"
  (words_as_type_indexed_bitvec)]
theorem NOT_0w_bis {width : Nat} [NeZero width] {w : BitVec width} : w ≠ 0 → 0 < w.toNat := by
  intro h
  exact Nat.pos_of_ne_zero fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))

/-- `dimwords n` is the `n`-th power of the word modulus. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "dimwords_dimword"
  (word_dimension_as_width := width)]
theorem dimwords_dimword (width : Nat) [NeZero width] :
    ∀ n : Nat, dimwords width n = (2 ^ width) ^ n := by
  intro n
  rw [dimwords, ← Nat.pow_mul, Nat.mul_comm]

/-- Appending a most-significant digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw2n_msf"
  (words_as_type_indexed_bitvec)]
theorem mw2n_msf {width : Nat} [NeZero width] :
    ∀ (x : BitVec width) (xs : List (BitVec width)),
      mw2n (xs ++ [x]) = mw2n xs + dimwords width xs.length * x.toNat := by
  intro x xs
  rw [mw2n_append]
  simp [mw2n]

/-- A value below the range of the leading digits ignores the last digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw2n_msf_NIL"
  (words_as_type_indexed_bitvec)]
theorem mw2n_msf_NIL {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width), xs ≠ [] ∧ mw2n xs < dimwords width xs.dropLast.length →
      mw2n xs = mw2n xs.dropLast := by
  rintro xs ⟨ne, lt⟩
  obtain ⟨ys, y, rfl⟩ := List.eq_nil_or_concat xs |>.resolve_left ne
  simp only [List.concat_eq_append, List.dropLast_concat] at lt ⊢
  rw [mw2n_msf] at lt ⊢
  have pos := dimwords_pos (width := width) ys.length
  have hy : y.toNat = 0 := Classical.byContradiction fun h => by
    have : dimwords width ys.length ≤ dimwords width ys.length * y.toNat :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h)
    omega
  rw [hy, Nat.mul_zero, Nat.add_zero]

/-- The zero expansion denotes zero. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw2n_k2mw_0"
  (words_as_type_indexed_bitvec)]
theorem mw2n_k2mw_0 {width : Nat} [NeZero width] :
    ∀ x : Nat, mw2n (k2mw x 0 : List (BitVec width)) = 0 := by
  intro x
  induction x with
  | zero => rfl
  | succ x ih => simp [k2mw, mw2n, ih]

/-- Multiplication by a single word: value and length. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_mul_by_single_lemma"
  (words_as_type_indexed_bitvec)]
theorem mwMulBySingle_lemma {width : Nat} [NeZero width] :
    ∀ (x : BitVec width) (ys : List (BitVec width)),
      mw2n (mwMulBySingle x ys) = x.toNat * mw2n ys ∧
        (mwMulBySingle x ys).length = ys.length + 1 := by
  intro x ys
  refine ⟨?_, length_mwMulBySingle⟩
  have := (mwMulPass_thm x ys (k2mw ys.length 0) 0 (length_k2mw _ _).symm).1
  simp only [mwMulBySingle, this, mw2n_k2mw_0]
  simp

end Flapjack.Misc.Multiword
