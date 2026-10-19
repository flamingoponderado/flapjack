/-
Copyright (c) 2025 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Flapjack.Compiler.Encoders.Arm8.Machine.ControlCase

/-!
# The ARM8 `jump_cmp` encoder-correctness case

This file develops the case of `encoder_correct arm8Target` for the comparison
branches `.jumpCmp cmp r ri a`.  A comparison branch lowers to two ARM8
instructions:

* a flag-setting instruction that computes `readReg r s?` against `regImm ri s?`
  (`logicalShiftedRegister`/`logicalImmediate` for the `test`/`notTest`
  comparisons, `addSubShiftedRegister`/`addSubImmediate` otherwise), and
* `branchConditional (a - 4) (cmpCond cmp)`.

The source semantics decides with `wordCmpHOL cmp (readReg r s1) (regImm ri s1)`,
so the proof has to identify the ARM8 condition code after the flag-setting
instruction with that `wordCmpHOL` value, and then transport both the taken and
the untaken successor state of `asmUpd` along the corresponding machine run.

The arithmetic half of that identification (`C`/`V`/`N`/`Z` of
`addWithCarry x (~~~y) true` against `BitVec.slt`) is proved here; the
instruction-level half and the two `CaseGoal` theorems are still to be
completed, hence this module currently contains no `@[hol]` tags.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-! ## Bitwise complements -/

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

/-- `cmpCond` emits a four-bit condition code. -/
theorem cmpCond_lt (cmp : Cmp) : cmpCond cmp < 16 := by
  cases cmp <;> decide

/-- The `cjump` offset window gives the twenty-one-bit branch guard for
`a - 4` together with its four-byte alignment. -/
theorem jumpCmp_cjumpOk_of_asm (a : BitVec 64)
    (h : asmCjumpOffsetOkExact arm8Config a = true) :
    fitsSigned 21 (a - 4) = true ∧ (a - 4).toNat % 4 = 0 := by
  simp only [asmCjumpOffsetOkExact, asmOffsetOkExact, arm8Config, Bool.and_eq_true] at h
  obtain ⟨⟨hlo, hhi⟩, hal⟩ := h
  have hlo := ofDecideTrue _ hlo
  have hhi := ofDecideTrue _ hhi
  have hmod : a.toNat % 4 = 0 := by simpa [asmAligned] using hal
  have hl : ((-1048572 : BitVec 64)).toInt = -1048572 := by decide
  have hh : ((1048579 : BitVec 64)).toInt = 1048579 := by decide
  rw [hl] at hlo
  rw [hh] at hhi
  have h4 : ((4 : BitVec 64)).toInt = 4 := by decide
  have hsub : (a - 4).toInt = a.toInt - 4 := by
    rw [BitVec.toInt_sub, h4]
    exact jumpCmp_bmod_self _ (by norm_num; omega) (by norm_num; omega)
  refine ⟨fitsSigned_of_range 21 (a - 4) (by decide) (by decide) ?_ ?_, ?_⟩
  · rw [hsub]; norm_num; omega
  · rw [hsub]; norm_num; omega
  · bv_omega

end Flapjack.Compiler.Encoders.Arm8
