module

public import Flapjack.Misc.Multiword.Mc.Iop
public import Flapjack.Misc.Multiword.DivMod
public import Flapjack.Misc.Multiword.DivLemmas
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/-! Definitions and lemmas of HOL's `mc_multiword` used to state the
correctness of the machine-code-style functions. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- The parity of a number is preserved modulo an even positive modulus. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "EVEN_MOD"]
theorem EVEN_MOD {m n : Nat} : 0 < m ∧ m % 2 = 0 → ((n % m) % 2 = 0 ↔ n % 2 = 0) := by
  rintro ⟨_, hm⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
  rw [Nat.mod_mod_of_dvd _ (Dvd.intro k rfl)]

/-- Encode a comparison outcome as a word. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "cmp2w_def"
  (words_as_type_indexed_bitvec)]
def cmp2w {width : Nat} [NeZero width] : Option Bool → BitVec width
  | none => 0
  | some true => 1
  | some false => 2

/-- The header word of a signed multiword number: twice its length, plus its sign. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_header_def"
  (words_as_type_indexed_bitvec)]
def mcHeader {width : Nat} [NeZero width] : Bool × List (BitVec width) → BitVec width
  | (s, xs) => BitVec.ofNat width (xs.length * 2) + if s then 1 else 0

/-- The lowest bit of a header is the sign. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_header_AND_1"
  (words_as_type_indexed_bitvec)]
theorem mcHeader_AND_1 {width : Nat} [NeZero width] {s : Bool} {xs : List (BitVec width)} :
    mcHeader (s, xs) &&& 1 = b2w s := by
  apply BitVec.eq_of_toNat_eq
  have pos := Nat.pos_of_ne_zero (NeZero.ne width)
  have lt1 : (1 : Nat) < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  have one : (1 : BitVec width).toNat = 1 := by simp [Nat.mod_eq_of_lt lt1]
  have zero : (0 : BitVec width).toNat = 0 := by simp
  have hw : 2 ^ width % 2 = 0 := by
    rw [show width = width - 1 + 1 by omega, Nat.pow_succ]; simp
  generalize hx : BitVec.ofNat width (xs.length * 2) = x
  have even : x.toNat % 2 = 0 := by
    rw [← hx, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hw)]
    simp [Nat.mul_mod_left]
  have xlt := x.isLt
  rw [BitVec.toNat_and, one, Nat.and_one_is_mod]
  cases s
  · have e : x + (0 : BitVec width) = x := by simp
    simp only [mcHeader, hx, Bool.false_eq_true, if_false, e, b2w, b2n]
    rw [even, BitVec.toNat_ofNat, Nat.zero_mod]
  · have small : x.toNat + 1 < 2 ^ width := by omega
    simp only [mcHeader, hx, if_true, b2w, b2n]
    rw [BitVec.toNat_add, one, Nat.mod_eq_of_lt small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt1]
    omega

/-- `b2w` is zero exactly for false and one exactly for true. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "b2w_eq"
  (words_as_type_indexed_bitvec)]
theorem b2w_eq {width : Nat} [NeZero width] {w2 : Nat} [NeZero w2] {b : Bool} :
    ((b2w b : BitVec width) = 0 ↔ ¬ b = true) ∧ ((b2w b : BitVec w2) = 1 ↔ b = true) := by
  have h1 : (1 : Nat) < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  have h2 : (1 : Nat) < 2 ^ w2 := Nat.one_lt_two_pow (NeZero.ne w2)
  cases b <;> simp [b2w, b2n, NeZero.ne]

/-- A most-significant zero digit does not change `mw_fix`. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mw_fix_SNOC"
  (words_as_type_indexed_bitvec)]
theorem mwFix_SNOC {width : Nat} [NeZero width] {xs : List (BitVec width)} :
    mwFix (xs ++ [0]) = mwFix xs := by
  rw [mwFix_snoc, if_pos rfl]

/-- The machine encoding of the arithmetic operations. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "int_op_rep_def"
  (words_as_type_indexed_bitvec)]
def intOpRep {width : Nat} [NeZero width] : MwOp → BitVec width
  | .add => 0
  | .sub => 1
  | .lt => 2
  | .eq => 3
  | .mul => 4
  | .div => 5
  | .mod => 6
  | .dec => 7

/-- The step budget of the machine-code division. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_div_max_def"
  (words_as_type_indexed_bitvec)]
def mcDivMax {width : Nat} [NeZero width] (xs ys zs : List (BitVec width)) : Nat :=
  2 * ys.length + 2 * zs.length + 5 + width + xs.length * (2 ^ width + 2 * ys.length + 4)

/-- Signed quotient or remainder, selected by a word. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mwi_divmod_alt_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwiDivmodAlt {width : Nat} [NeZero width] {w2 : Nat} [NeZero w2]
    (w : BitVec w2) (s_xs t_ys : Bool × List (BitVec width)) : Bool × List (BitVec width) :=
  if w = 0 then mwiDiv s_xs t_ys else mwiMod s_xs t_ys

/-- The top bit is set exactly when doubling and halving loses it. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "word_msb_double_lsr_1"
  (words_as_type_indexed_bitvec)]
theorem word_msb_double_lsr_1 {width : Nat} [NeZero width] {w : BitVec width} :
    w.msb = true ↔ w ≠ (w + w) >>> 1 := by
  have pos := Nat.pos_of_ne_zero (NeZero.ne width)
  have hw : 2 ^ width = 2 * 2 ^ (width - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hlt := w.isLt
  have key : ((w + w) >>> 1).toNat =
      if w.toNat < 2 ^ (width - 1) then w.toNat else w.toNat - 2 ^ (width - 1) := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, Nat.shiftRight_eq_div_pow, pow_one]
    split
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  rw [BitVec.msb_eq_decide, decide_eq_true_iff, Ne, ← BitVec.toNat_inj, key]
  constructor
  · intro h; split <;> omega
  · intro h; split at h <;> omega

/-- Setting a clear low bit by exclusive or adds one. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "xor_one_add_one"
  (words_as_type_indexed_bitvec)]
theorem xor_one_add_one {width : Nat} [NeZero width] {w : BitVec width} :
    ¬ w.getLsbD 0 = true → w ^^^ 1 = w + 1 := by
  intro h
  have h1 : (1 : Nat) < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  have ev : w.toNat % 2 = 0 := by
    rw [BitVec.getLsbD, Nat.testBit_zero] at h
    simp at h; omega
  have dvd : 2 ∣ 2 ^ width := dvd_pow_self 2 (NeZero.ne width)
  have hlt := w.isLt
  have small : w.toNat + 1 < 2 ^ width := by
    obtain ⟨k, hk⟩ := dvd; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_add]
  have one : (1 : BitVec width).toNat = 1 := by simp [Nat.mod_eq_of_lt h1]
  rw [one, Nat.xor_one_of_even (Nat.even_iff.mpr ev), Nat.mod_eq_of_lt small]

/-- Adding one to a word with a clear low bit is undone by exclusive or. -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "add_one_xor_one"
  (words_as_type_indexed_bitvec)]
theorem add_one_xor_one {width : Nat} [NeZero width] {w : BitVec width} :
    ¬ w.getLsbD 0 = true → (w + 1) ^^^ 1 = w := by
  intro h
  rw [← xor_one_add_one h]
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

end Flapjack.Misc.Multiword
