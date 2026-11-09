module

public import Flapjack.HolRef
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Multiword integer encodings from the HOL multiword library. -/
namespace Flapjack.Misc.Multiword

/-- Natural number represented as little-endian word digits. The production
constant compiler uses it through `i2mw`. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "n2mw_def"
  (words_as_type_indexed_bitvec)]
def n2mw {width : Nat} [NeZero width] (n : Nat) : List (BitVec width) :=
  if n = 0 then [] else
    BitVec.ofNat width (n % 2 ^ width) :: n2mw (n / 2 ^ width)
termination_by n
decreasing_by
  apply Nat.div_lt_self (by omega)
  exact Nat.one_lt_two_pow (NeZero.ne width)

/-- Signed integer represented by its sign and magnitude words. The production
constant compiler uses this definition directly. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "i2mw_def"
  (words_as_type_indexed_bitvec)]
def i2mw {width : Nat} [NeZero width] (i : Int) : Bool × List (BitVec width) :=
  (decide (i < 0), n2mw i.natAbs)

/-- Interpret little-endian word digits as a natural number. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw2n_def"
  (words_as_type_indexed_bitvec)]
def mw2n {width : Nat} [NeZero width] : List (BitVec width) → Nat
  | [] => 0
  | x :: xs => x.toNat + 2 ^ width * mw2n xs

/-- Compare word lists from the most significant end, preserving HOL's
unspecified `LAST []` when the second list is shorter. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_cmp_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwCmp {width : Nat} [NeZero width] (xs ys : List (BitVec width)) : Option Bool :=
  if xs = [] then none
  else if holLast xs = holLast ys then mwCmp xs.dropLast ys.dropLast
  else some (decide (holLast xs < holLast ys))
termination_by xs.length
decreasing_by
  simp only [List.length_dropLast]
  cases xs <;> simp_all

/-- Decode a sign-and-magnitude representation as a signed integer. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw2i_def"
  (words_as_type_indexed_bitvec)]
def mw2i {width : Nat} [NeZero width] : Bool × List (BitVec width) → Int
  | (false, xs) => Int.ofNat (mw2n xs)
  | (true, xs) => -Int.ofNat (mw2n xs)

/-- Converting a natural to words and back preserves its value. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw2n_n2mw"
  (words_as_type_indexed_bitvec)]
theorem mw2n_n2mw {width : Nat} [NeZero width] (n : Nat) : mw2n (n2mw n : List (BitVec width)) = n := by
  rw [n2mw]
  split
  · simp_all [mw2n]
  · simp only [mw2n, BitVec.toNat_ofNat, Nat.mod_mod]
    rw [mw2n_n2mw (n / 2 ^ width)]
    exact Nat.mod_add_div n (2 ^ width)
termination_by n
decreasing_by
  apply Nat.div_lt_self (by omega)
  exact Nat.one_lt_two_pow (NeZero.ne width)

/-- Converting an integer to signed words and back preserves its value. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw2i_i2mw"
  (words_as_type_indexed_bitvec)]
theorem mw2i_i2mw {width : Nat} [NeZero width] (i : Int) : mw2i (i2mw i : Bool × List (BitVec width)) = i := by
  cases i with
  | ofNat n =>
    have nonnegative : ¬ (Int.ofNat n < 0) := by
      rw [Int.ofNat_eq_natCast]
      exact Int.not_lt_of_ge (Int.natCast_nonneg n)
    change mw2i (decide (Int.ofNat n < 0), n2mw (Int.ofNat n).natAbs) = Int.ofNat n
    rw [show decide (Int.ofNat n < 0) = false from decide_eq_false nonnegative]
    simp [mw2i, mw2n_n2mw]
  | negSucc n =>
    change mw2i (decide (Int.negSucc n < 0), n2mw (Int.negSucc n).natAbs) = Int.negSucc n
    simp only [Int.negSucc_lt_zero, decide_true, Int.natAbs_negSucc, mw2i, mw2n_n2mw]
    rw [Int.negSucc_eq]
    simp

end Flapjack.Misc.Multiword
