module

public import Flapjack.Compiler.Encoders.Asm
public import Mathlib.Data.BitVec
public import Mathlib.Tactic

@[expose] public section

/-!
# Shared ARMv8 arithmetic and flag lemmas

Carrier-independent facts used by both the closed ARMv8 machine model
(`Machine/`) and the L3 ARMv8 encoder-correctness chain
(`L3/CorrectnessEncoding/`).  They mention only `BitVec`, `Int`, `Nat` and the
pure flag tuple `Arm8Flags`, so they live here rather than being copied into
both trees.  `addWithCarry` is the architectural `AddWithCarry` value/flag
pair at 64 bits; the flag lemmas identify its carry, zero and signed-less-than
behaviour, and the `addFlags`/`subFlags` helpers give the flag-setting
add/sub forms.

No HOL claim is introduced here: these are the arithmetic facts both
renderings of the ARMv8 target share.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm

/-- ARM condition flags in the order `N`, `Z`, `C`, `V`. -/
abbrev Arm8Flags := Bool × Bool × Bool × Bool



/-- `AddWithCarry` of the L3 ARM8 model, at 64 bits. -/
def addWithCarry (x y : BitVec 64) (carryIn : Bool) : BitVec 64 × Arm8Flags :=
  let unsignedSum : Nat := x.toNat + y.toNat + (if carryIn then 1 else 0)
  let result : BitVec 64 := BitVec.ofNat 64 unsignedSum
  let n := result.getLsbD 63
  let z := result = 0
  let c := result.toNat ≠ unsignedSum
  let v := result.toInt ≠ x.toInt + y.toInt + (if carryIn then 1 else 0)
  (result, (n, z, c, v))


/-! ## Word arithmetic used by the instruction models -/

/-- `ofNat` of the sum of the `toNat`s is the word sum. -/
theorem arith_ofNat64_add_toNat (x y : BitVec 64) :
    BitVec.ofNat 64 (x.toNat + y.toNat) = x + y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_add]

/-- The result half of `addWithCarry` without carry. -/
theorem arith_addWithCarry_false (x y : BitVec 64) :
    (addWithCarry x y false).1 = x + y := by
  unfold addWithCarry
  simp only [Bool.false_eq_true, if_false, Nat.add_zero]
  exact arith_ofNat64_add_toNat x y

/-- `ofNat` of a sum with one extra low bit is the word sum with one. -/
theorem arith_ofNat64_add_one (x y : BitVec 64) :
    BitVec.ofNat 64 (x.toNat + y.toNat + 1) = x + y + 1 := by
  rw [show x.toNat + y.toNat + 1 = (x.toNat + y.toNat) + 1 by omega]
  rw [BitVec.ofNat_add, arith_ofNat64_add_toNat]
  rfl

/-- The result half of `addWithCarry` with carry in. -/
theorem arith_addWithCarry_true (x y : BitVec 64) :
    (addWithCarry x y true).1 = x + y + 1 := by
  unfold addWithCarry
  simp only [if_true]
  exact arith_ofNat64_add_one x y

/-- The value `x + ~~~y + 1` is the difference `x - y`. -/
theorem arith_add_not_add_one (x y : BitVec 64) : x + ~~~y + 1 = x - y := by
  rw [BitVec.add_assoc]
  have h1 : (1 : BitVec 64) = 1#64 := rfl
  rw [h1, ← BitVec.neg_eq_not_add, BitVec.sub_eq_add_neg]


/-- `toNat` of a sixty-four-bit complement. -/
theorem jumpCmp_toNat_not (y : BitVec 64) : (~~~y).toNat = 2 ^ 64 - 1 - y.toNat := by
  bv_omega

/-- `toInt` of a sixty-four-bit complement. -/
theorem jumpCmp_toInt_not (y : BitVec 64) : (~~~y).toInt = -1 - y.toInt := by
  rw [BitVec.toInt_not]
  apply (Int.bmod_eq_iff (by norm_num : (0 : Nat) < 2 ^ 64)).2
  have hy1 := BitVec.toInt_lt (x := y)
  have hy2 := BitVec.le_toInt (x := y)
  refine ⟨by omega, by omega, ?_⟩
  have hy := y.toInt_eq_toNat_cond
  split at hy
  · rw [hy]; exact ⟨-1, by omega⟩
  · rw [hy]; exact ⟨0, by omega⟩

/-! ## `addWithCarry` on a complemented operand -/

/-- The value of `addWithCarry x (~~~y) true` is `x - y`. -/
theorem jumpCmp_addWithCarry_val (x y : BitVec 64) :
    (addWithCarry x (~~~y) true).1 = x - y := by
  simp [addWithCarry]
  bv_omega

/-- The carry-out of `addWithCarry x (~~~y) true` is `!(x < y)`. -/
theorem jumpCmp_flags_c (x y : BitVec 64) :
    (addWithCarry x (~~~y) true).2.2.2.1 = !(x.ult y) := by
  rw [BitVec.ult_eq_not_carry]
  simp only [Bool.not_not]
  have hc : BitVec.carry 64 x (~~~y) true =
      decide (x.toNat + (~~~y).toNat + 1 ≥ 2 ^ 64) := by
    simp only [BitVec.carry, Nat.mod_eq_of_lt x.isLt]
    rw [jumpCmp_toNat_not, Nat.mod_eq_of_lt (by omega : 2 ^ 64 - 1 - y.toNat < 2 ^ 64)]
    rfl
  rw [hc]
  show decide ((addWithCarry x (~~~y) true).1.toNat ≠
    x.toNat + (~~~y).toNat + (if true = true then 1 else 0)) = _
  simp only [if_true]
  rw [decide_eq_decide]
  rw [show (addWithCarry x (~~~y) true).1.toNat =
    (x.toNat + (~~~y).toNat + 1) % 2 ^ 64 from rfl]
  have hx := x.isLt
  have hy := y.isLt
  have hy' := jumpCmp_toNat_not y
  constructor
  · intro h
    by_cases hxy : x.toNat + (2^64 - 1 - y.toNat) + 1 < 2^64
    · have hmod : (x.toNat + (~~~y).toNat + 1) % 2^64 = x.toNat + (~~~y).toNat + 1 := by
        rw [show x.toNat + (~~~y).toNat + 1 = x.toNat + (2^64 - 1 - y.toNat) + 1 from by
          rw [hy']]
        exact Nat.mod_eq_of_lt hxy
      rw [hmod] at h
      exact absurd rfl h
    · omega
  · intro h
    have hle : y.toNat ≤ x.toNat := by omega
    have hsub : x.toNat + (~~~y).toNat + 1 = (x.toNat - y.toNat) + 2^64 := by
      rw [hy']; omega
    rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The zero flag of `addWithCarry x (~~~y) true` is `x = y`. -/
theorem jumpCmp_flags_z (x y : BitVec 64) :
    (addWithCarry x (~~~y) true).2.2.1 = decide (x = y) := by
  show decide ((addWithCarry x (~~~y) true).1 = 0) = decide (x = y)
  rw [jumpCmp_addWithCarry_val]
  rw [decide_eq_decide, BitVec.sub_eq_iff_eq_add]
  simp

/-! ## Signed comparison from the `N` and `V` flags -/

/-- `getLsbD 63` records the sign of the `toInt` value. -/
theorem jumpCmp_getLsbD_last (r : BitVec 64) :
    r.getLsbD 63 = decide (r.toInt < 0) := by
  rw [BitVec.getLsbD_last, decide_eq_decide, BitVec.toInt_neg_iff]
  have h := r.isLt
  omega

/-- `bmod` into `[-(2^63), 2^63)` is the identity. -/
theorem jumpCmp_bmod_self (S : Int) (hlo : -(2 ^ 63) ≤ S) (hhi : S < 2 ^ 63) :
    S.bmod (2 ^ 64) = S := by
  apply (Int.bmod_eq_iff (by norm_num : (0 : Nat) < 2 ^ 64)).2
  refine ⟨?_, ?_, ?_⟩
  · norm_num; omega
  · norm_num; omega
  · exact ⟨0, by norm_num⟩

/-- A value just below zero wraps to `S + 2^64`. -/
theorem jumpCmp_bmod_add (S : Int) (hlo : 0 ≤ S + 2 ^ 64)
    (hhi : S + 2 ^ 64 < 2 ^ 63) : S.bmod (2 ^ 64) = S + 2 ^ 64 := by
  apply (Int.bmod_eq_iff (by norm_num : (0 : Nat) < 2 ^ 64)).2
  refine ⟨?_, ?_, ?_⟩
  · norm_num; omega
  · norm_num; omega
  · exact ⟨1, by norm_num⟩

/-- A non-negative value at least `2^63` wraps to `S - 2^64`. -/
theorem jumpCmp_bmod_sub (S : Int) (hlo : -(2 ^ 63) ≤ S - 2 ^ 64)
    (hhi : S - 2 ^ 64 < 0) : S.bmod (2 ^ 64) = S - 2 ^ 64 := by
  apply (Int.bmod_eq_iff (by norm_num : (0 : Nat) < 2 ^ 64)).2
  refine ⟨?_, ?_, ?_⟩
  · norm_num; omega
  · norm_num; omega
  · exact ⟨-1, by norm_num⟩

/-- The `N`/`V` pair is `true` exactly for a negative signed difference. -/
theorem jumpCmp_flags_slt_prop (S : Int) (hlo : -(2 ^ 64 - 1) ≤ S) (hhi : S ≤ 2 ^ 64 - 1) :
    (decide (S.bmod (2 ^ 64) < 0) != decide (S.bmod (2 ^ 64) ≠ S)) = decide (S < 0) := by
  by_cases hs : S < 0
  · have key : (decide (S.bmod (2 ^ 64) < 0) != decide (S.bmod (2 ^ 64) ≠ S)) = true := by
      by_cases hlow : S < -(2 ^ 63)
      · have hb : S.bmod (2 ^ 64) = S + 2 ^ 64 := jumpCmp_bmod_add S (by omega) (by omega)
        rw [hb, show decide (S + 2 ^ 64 < 0) = false from
          decide_eq_false_iff_not.mpr (by omega),
          show decide (S + 2 ^ 64 ≠ S) = true from decide_eq_true_eq.mpr (by omega)]
        rfl
      · have hb : S.bmod (2 ^ 64) = S := jumpCmp_bmod_self S (by omega) (by omega)
        rw [hb, show decide (S < 0) = true from decide_eq_true_eq.mpr hs,
          show decide (S ≠ S) = false from decide_eq_false_iff_not.mpr (by simp)]
        rfl
    rw [key, show decide (S < 0) = true from decide_eq_true_eq.mpr hs]
  · have key : (decide (S.bmod (2 ^ 64) < 0) != decide (S.bmod (2 ^ 64) ≠ S)) = false := by
      by_cases hhigh : S < 2 ^ 63
      · have hb : S.bmod (2 ^ 64) = S := jumpCmp_bmod_self S (by omega) (by omega)
        rw [hb, show decide (S < 0) = false from decide_eq_false_iff_not.mpr hs,
          show decide (S ≠ S) = false from decide_eq_false_iff_not.mpr (by simp)]
        rfl
      · have hb : S.bmod (2 ^ 64) = S - 2 ^ 64 := jumpCmp_bmod_sub S (by omega) (by omega)
        rw [hb, show decide (S - 2 ^ 64 < 0) = true from decide_eq_true_eq.mpr (by omega),
          show decide (S - 2 ^ 64 ≠ S) = true from decide_eq_true_eq.mpr (by omega)]
        rfl
    rw [key, show decide (S < 0) = false from decide_eq_false_iff_not.mpr hs]

/-- The `N`/`V` pair of `addWithCarry x (~~~y) true` is `x.slt y`. -/
theorem jumpCmp_flags_slt (x y : BitVec 64) :
    ((addWithCarry x (~~~y) true).2.1 != (addWithCarry x (~~~y) true).2.2.2.2) =
      x.slt y := by
  set B := (x.toInt - y.toInt).bmod (2 ^ 64) with hB
  have hr : (addWithCarry x (~~~y) true).1.toInt = B := by
    rw [jumpCmp_addWithCarry_val, BitVec.toInt_sub]
  have hn : (addWithCarry x (~~~y) true).2.1 = decide (B < 0) := by
    show (addWithCarry x (~~~y) true).1.getLsbD 63 = _
    rw [jumpCmp_getLsbD_last, hr]
  have hv : (addWithCarry x (~~~y) true).2.2.2.2 = decide (B ≠ x.toInt - y.toInt) := by
    show decide ((addWithCarry x (~~~y) true).1.toInt ≠
      x.toInt + (~~~y).toInt + (if true = true then 1 else 0)) = _
    rw [jumpCmp_toInt_not, hr]
    rw [if_pos rfl]
    rw [show x.toInt + (-1 - y.toInt) + 1 = x.toInt - y.toInt from by omega]
  rw [hn, hv, BitVec.slt_eq_decide, hB]
  have hx1 := BitVec.toInt_lt (x := x)
  have hx2 := BitVec.le_toInt (x := x)
  have hy1 := BitVec.toInt_lt (x := y)
  have hy2 := BitVec.le_toInt (x := y)
  rw [jumpCmp_flags_slt_prop (x.toInt - y.toInt) (by omega) (by omega)]
  rw [show decide (x.toInt - y.toInt < 0) = decide (x.toInt < y.toInt) from by
    rw [decide_eq_decide]; constructor <;> intro h <;> omega]

/-! ## Encoder side conditions -/



/-- `holAsmSignedLess` is `BitVec.slt`. -/
theorem jumpCmp_holAsmSignedLess_eq (a b : BitVec 64) : holAsmSignedLess a b = a.slt b := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_toNat_cond]
  split <;> split <;> simp <;> omega


/-- The flags `addWithCarry` produces, in terms of its own result. -/
theorem addWithCarry_flags (x y : BitVec 64) (cin : Bool) :
    (addWithCarry x y cin).2 =
      ((addWithCarry x y cin).1.getLsbD 63, decide ((addWithCarry x y cin).1 = 0),
       decide ((addWithCarry x y cin).1.toNat ≠ x.toNat + y.toNat + (if cin then 1 else 0)),
       decide ((addWithCarry x y cin).1.toInt ≠ x.toInt + y.toInt + (if cin then 1 else 0))) :=
  rfl

/-- The flags of a flag-setting addition without carry. -/
def addFlags (x y : BitVec 64) : Arm8Flags :=
  let r := x + y
  (r.getLsbD 63, decide (r = 0), decide (r.toNat ≠ x.toNat + y.toNat),
    decide (r.toInt ≠ x.toInt + y.toInt))

/-- The flags of a flag-setting subtraction. -/
def subFlags (x y : BitVec 64) : Arm8Flags :=
  let r := x - y
  (r.getLsbD 63, decide (r = 0), decide (r.toNat ≠ x.toNat + (~~~y).toNat + 1),
    decide (r.toInt ≠ x.toInt + (~~~y).toInt + 1))

/-- `addWithCarry` on an uncomplemented second operand, without carry. -/
theorem addWithCarry_addFlags (x y : BitVec 64) :
    addWithCarry x y false = (x + y, addFlags x y) := by
  refine Prod.ext ?_ ?_
  · show (addWithCarry x y false).1 = x + y
    rw [arith_addWithCarry_false]
  · show (addWithCarry x y false).2 = addFlags x y
    rw [addWithCarry_flags, arith_addWithCarry_false]
    simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero, Nat.add_zero, addFlags]

/-- `addWithCarry` on a complemented second operand, with carry. -/
theorem addWithCarry_subFlags (x y : BitVec 64) :
    addWithCarry x (~~~y) true = (x - y, subFlags x y) := by
  refine Prod.ext ?_ ?_
  · show (addWithCarry x (~~~y) true).1 = x - y
    rw [arith_addWithCarry_true, arith_add_not_add_one]
  · show (addWithCarry x (~~~y) true).2 = subFlags x y
    rw [addWithCarry_flags, arith_addWithCarry_true, arith_add_not_add_one]
    simp only [↓reduceIte, subFlags]

/-- The overflow flag of a flag-setting addition. -/
theorem addFlags_v (x y : BitVec 64) :
    (addFlags x y).2.2.2 = decide ((x + y).toInt ≠ x.toInt + y.toInt) := rfl

/-- The overflow flag of a flag-setting subtraction. -/
theorem subFlags_v (x y : BitVec 64) :
    (subFlags x y).2.2.2 = decide ((x - y).toInt ≠ x.toInt - y.toInt) := by
  have h : x.toInt + (~~~y).toInt + 1 = x.toInt - y.toInt := by
    rw [jumpCmp_toInt_not]; omega
  rw [subFlags, h]


/-- A `Bool` that is not `true` is `false`. -/
theorem boolOfNotTrue {b : Bool} (h : ¬(b = true)) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd rfl h


end Flapjack.Compiler.Encoders.Arm8
