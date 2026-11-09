module

public import Flapjack.Compiler.Backend.DataToWord.Numbers
public import Flapjack.Misc.Multiword

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Agreement with Flapjack's former executable immediate-integer encoding. -/
namespace Flapjack.Compiler.Backend.DataToWord
open Flapjack

/-- Flapjack-specific equality between the original sliced mask and the
previous compiler's arithmetic mask, including out-of-range bit positions. -/
theorem allOnes_eq_inlined {width : Nat} [NeZero width] (bits shift : Nat) :
    allOnes (width := width) (shift + bits) shift =
      BitVec.ofNat width ((2 ^ bits - 1) * 2 ^ shift) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hb : bits = 0
  · subst bits; simp [allOnes]
  · have hnot : ¬ shift + bits ≤ shift := by omega
    simp only [allOnes, hnot, ↓reduceIte, holWordSlice, getLsbD_holFcpWord,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
      Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
    have hz : (0 : BitVec width).getLsbD i = false := by simp
    rw [hz]
    simp only [Bool.not_false, Bool.and_true]
    by_cases hs : shift ≤ i
    · by_cases hl : i - shift < bits
      · have hiBound : i ≤ min (shift + bits - 1) (width - 1) := by omega
        simp [hs, hl, hiBound]
      · have hiBound : ¬ i ≤ min (shift + bits - 1) (width - 1) := by omega
        simp [hs, hl, hiBound]
    · simp [hs]

/-- A left shift of a converted natural is its modular power-of-two product. -/
theorem shift_eq_inlined {width : Nat} (n shift : Nat) :
    (BitVec.ofNat width n <<< shift) = BitVec.ofNat width (n * 2 ^ shift) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_mod]

/-- Each source field encoding equals the former compiler field formula. -/
theorem maxoutBits_eq_inlined {width : Nat} [NeZero width] (n bits shift : Nat) :
    maxoutBits (width := width) n bits shift =
      BitVec.ofNat width ((if n < 2 ^ bits - 1 then n else 2 ^ bits - 1) * 2 ^ shift) := by
  by_cases h : n < 2 ^ bits - 1 <;>
    simp [maxoutBits, h, shift_eq_inlined, allOnes_eq_inlined]

/-- The source pointer annotation agrees with the formerly inlined compiler
formula for every configuration, tag, length, and positive width. -/
theorem ptrBits_eq_inlined {width : Nat} [NeZero width] (conf : Config) (tag len : Nat) :
    ptrBits (width := width) conf tag len =
      (let field (n bits shift : Nat) : BitVec width :=
        let maximum := 2 ^ bits - 1
        BitVec.ofNat width ((if n < maximum then n else maximum) * 2 ^ shift)
       field tag conf.tagBits (1 + conf.lenBits) ||| field len conf.lenBits 1) := by
  simp [ptrBits, maxoutBits_eq_inlined]

/-- Flapjack-specific equivalence with the previously inlined compiler formula;
it holds for every integer and positive width, not only for small integers. -/
theorem smallnum_eq_inlined {width : Nat} [NeZero width] (i : Int) :
    smallnum (width := width) i =
      (if i < 0 then -(BitVec.ofNat width (4 * i.natAbs)) else BitVec.ofNat width (4 * i.natAbs)) := by
  cases i with
  | ofNat n =>
      have h : ¬ ((n : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg n)
      simp [smallnum, h, Int.natAbs, Int.toNat_mul (a := 4) (b := (n : Int)) (by decide) (Int.natCast_nonneg n)]
  | negSucc n =>
      have h : Int.negSucc n < 0 := by omega
      have hn : 0 ≤ (n : Int) + 1 := by omega
      simp [smallnum, h, Int.natAbs, Int.toNat_mul (a := 4) (b := (n : Int) + 1) (by decide) hn]

/-- The previously executed bounded digit traversal, retained as the left
side of the compiler-agreement theorem. -/
private def oldDigits {width : Nat} (fuel n : Nat) : List (BitVec width) :=
  match fuel with
  | 0 => []
  | fuel + 1 => if n == 0 then [] else
      BitVec.ofNat width (n % (2 ^ width)) :: oldDigits fuel (n / (2 ^ width))

/-- Flapjack-specific agreement with the former bounded compiler traversal.
Its original fuel is `n + 1`, which satisfies this sufficient bound. -/
theorem oldDigits_eq_n2mw {width : Nat} [NeZero width] (fuel n : Nat) (bound : n < fuel) :
    oldDigits (width := width) fuel n = Misc.Multiword.n2mw n := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
      by_cases hn : n = 0
      · subst n; simp [oldDigits, Misc.Multiword.n2mw]
      · have hnPos : 0 < n := by omega
        have quotient : n / 2 ^ width < n := Nat.div_lt_self hnPos (Nat.one_lt_two_pow (NeZero.ne width))
        have next : n / 2 ^ width < fuel := by omega
        simp only [oldDigits, beq_iff_eq, hn, ↓reduceIte]
        rw [Misc.Multiword.n2mw]
        simp only [hn, ↓reduceIte]
        rw [ih _ next]

end Flapjack.Compiler.Backend.DataToWord
