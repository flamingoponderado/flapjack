/-
Copyright (c) 2025 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Flapjack.Compiler.Encoders.Arm8.Machine.ControlCase
import Flapjack.Compiler.Encoders.Arm8.Machine.MaskConverses

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
`addWithCarry x (~~~y) true` against `BitVec.slt`) and the instruction-level
half are both proved here: `jumpCmpCase` turns them, together with a `StepSafe`
start and the two bytes facts of `asmUpd`, into the `CaseGoal`, and
`case_jumpCmp_reg`/`case_jumpCmp_imm` specialise it to the two `reg_imm`
operands.

Like the other cases in `Machine/ControlCase.lean`, these two are case splits
of the single HOL theorem `arm8_encoder_correct`
(`cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml`), whose
`JumpCmp` branch has no per-case declaration of its own; they are Flapjack
infrastructure and this module therefore carries no `@[hol]` tags.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

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
  simp only [ite_true]
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
    rw [ite_eq_left rfl]
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

/-! ## The condition code of a comparison

The source semantics decides a comparison branch with
`wordCmpHOL cmp (readReg r s1) (regImm ri s1)`; the target evaluates the
condition code `cmpCond cmp` against the flags the preceding instruction
writes.  The lemmas below identify the two. -/

/-- `holAsmSignedLess` is `BitVec.slt`. -/
theorem jumpCmp_holAsmSignedLess_eq (a b : BitVec 64) : holAsmSignedLess a b = a.slt b := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_toNat_cond]
  split <;> split <;> simp <;> omega

/-- Boolean equality is decided equality (over a lawful `BEq`). -/
theorem jumpCmp_decide_eq_beq {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (a b : α) :
    decide (a = b) = (a == b) := by
  cases hb : (a == b) with
  | false => exact decide_eq_false_iff_not.mpr (beq_eq_false_iff_ne.mp hb)
  | true => exact decide_eq_true_eq.mpr (beq_iff_eq.mp hb)

/-- Boolean inequality is decided inequality. -/
theorem jumpCmp_decide_ne_bne (a b : Bool) : decide (a ≠ b) = (a != b) := by
  cases a <;> cases b <;> rfl

/-- Boolean equality is the negation of decided inequality. -/
theorem jumpCmp_decide_eq_not_bne (a b : Bool) : decide (a = b) = !(a != b) := by
  cases a <;> cases b <;> rfl

/-! ### The flags the four flag-setting instructions write -/

/-- The zero flag after the flag-setting `AND` of two registers. -/
theorem execInsn_and_reg_z (s : Arm8State) (r u : Nat) :
    (execInsn { s with pc := s.pc + 4 }
      (.logicalShiftedRegister .and false true .lsl 0 u r 31)).z
      = decide (readReg s r &&& readReg s u = 0) := by
  simp [execInsn, writeReg, shiftValue, readReg, writeFlags]

/-- The flag projections of `writeFlags`. -/
theorem writeFlags_fst (s : Arm8State) (f : Arm8Flags) : (writeFlags s f).n = f.1 := rfl

/-- The zero-flag projection of `writeFlags`. -/
theorem writeFlags_snd_fst (s : Arm8State) (f : Arm8Flags) : (writeFlags s f).z = f.2.1 := rfl

/-- The carry-flag projection of `writeFlags`. -/
theorem writeFlags_snd_snd_fst (s : Arm8State) (f : Arm8Flags) :
    (writeFlags s f).c = f.2.2.1 := rfl

/-- The overflow-flag projection of `writeFlags`. -/
theorem writeFlags_snd_snd_snd (s : Arm8State) (f : Arm8Flags) :
    (writeFlags s f).v = f.2.2.2 := rfl

/-- The flags after the flag-setting `SUB` of two registers. -/
theorem execInsn_addSub_reg_flags (s : Arm8State) (r u : Nat) :
    execInsn { s with pc := s.pc + 4 } (.addSubShiftedRegister true true .lsl u 0 r 31)
      = writeFlags { s with pc := s.pc + 4 }
          (addWithCarry (readReg s r) (~~~(readReg s u)) true).2 := by
  simp [execInsn, writeReg, shiftValue, readReg]

/-- The zero flag after the flag-setting `AND` with an immediate. -/
theorem execInsn_and_imm_z (s : Arm8State) (r : Nat) (w : BitVec 64) :
    (execInsn { s with pc := s.pc + 4 } (.logicalImmediate .and true w r 31)).z
      = decide (readReg s r &&& w = 0) := by
  simp [execInsn, writeReg, readReg, writeFlags]

/-- The flags after the flag-setting `SUB` with an immediate. -/
theorem execInsn_addSub_imm_flags (s : Arm8State) (r : Nat) (w : BitVec 64) :
    execInsn { s with pc := s.pc + 4 } (.addSubImmediate true true w r 31)
      = writeFlags { s with pc := s.pc + 4 }
          (addWithCarry (readReg s r) (~~~w) true).2 := by
  simp [execInsn, writeReg, readReg]

/-- The `test` condition code against the flags of an `AND`. -/
theorem conditionHolds_test (s : Arm8State) (x y : BitVec 64)
    (hz : s.z = decide (x &&& y = 0)) :
    conditionHolds s (cmpCond .test) = wordCmpHOL .test x y := by
  simp only [cmpCond, conditionHolds, hz, wordCmpHOL, AndOp.and, jumpCmp_decide_eq_beq]
  rfl

/-- The `notTest` condition code against the flags of an `AND`. -/
theorem conditionHolds_notTest (s : Arm8State) (x y : BitVec 64)
    (hz : s.z = decide (x &&& y = 0)) :
    conditionHolds s (cmpCond .notTest) = wordCmpHOL .notTest x y := by
  simp only [cmpCond, conditionHolds, hz, wordCmpHOL, AndOp.and, jumpCmp_decide_eq_beq]
  simp [bne]

/-- The condition code of a non-`test` comparison against the four flags of
`addWithCarry x (~~~y) true`, i.e. of the subtraction `x - y`. -/
theorem conditionHolds_addSub (s : Arm8State) (cmp : Cmp) (x y : BitVec 64)
    (hn : s.n = (addWithCarry x (~~~y) true).2.1)
    (hz : s.z = (addWithCarry x (~~~y) true).2.2.1)
    (hc : s.c = (addWithCarry x (~~~y) true).2.2.2.1)
    (hv : s.v = (addWithCarry x (~~~y) true).2.2.2.2)
    (hNT : isTest cmp = false) :
    conditionHolds s (cmpCond cmp) = wordCmpHOL cmp x y := by
  cases cmp
  case equal =>
    simp only [cmpCond, conditionHolds, hz, jumpCmp_flags_z, wordCmpHOL,
      jumpCmp_decide_eq_beq]
  case lower =>
    simp only [cmpCond, conditionHolds, hc, jumpCmp_flags_c, wordCmpHOL,
      BitVec.ult_eq_decide_lt, Bool.not_not]
  case less =>
    simp only [cmpCond, conditionHolds, hn, hv, jumpCmp_flags_slt,
      jumpCmp_holAsmSignedLess_eq, wordCmpHOL, jumpCmp_decide_ne_bne]
  case test => simp [isTest] at hNT
  case notEqual =>
    simp only [cmpCond, conditionHolds, hz, jumpCmp_flags_z, wordCmpHOL,
      jumpCmp_decide_eq_beq]
  case notLower =>
    simp only [cmpCond, conditionHolds, hc, jumpCmp_flags_c, wordCmpHOL,
      BitVec.ult_eq_decide_lt]
  case notLess =>
    simp only [cmpCond, conditionHolds, hn, hv, jumpCmp_decide_eq_not_bne,
      jumpCmp_flags_slt, jumpCmp_holAsmSignedLess_eq, wordCmpHOL]
  case notTest => simp [isTest] at hNT

/-- The condition code after the flag-setting `AND` of two registers. -/
theorem conditionHolds_and_reg (s : Arm8State) (cmp : Cmp) (r u : Nat)
    (hT : isTest cmp = true) :
    conditionHolds (execInsn { s with pc := s.pc + 4 }
        (.logicalShiftedRegister .and false true .lsl 0 u r 31)) (cmpCond cmp)
      = wordCmpHOL cmp (readReg s r) (readReg s u) := by
  cases cmp
  · simp [isTest] at hT
  · simp [isTest] at hT
  · simp [isTest] at hT
  · exact conditionHolds_test _ _ _ (execInsn_and_reg_z s r u)
  · simp [isTest] at hT
  · simp [isTest] at hT
  · simp [isTest] at hT
  · exact conditionHolds_notTest _ _ _ (execInsn_and_reg_z s r u)

/-- The condition code after the flag-setting `SUB` of two registers. -/
theorem conditionHolds_addSub_reg (s : Arm8State) (cmp : Cmp) (r u : Nat)
    (hNT : isTest cmp = false) :
    conditionHolds (execInsn { s with pc := s.pc + 4 }
        (.addSubShiftedRegister true true .lsl u 0 r 31)) (cmpCond cmp)
      = wordCmpHOL cmp (readReg s r) (readReg s u) := by
  cases cmp
  · exact conditionHolds_addSub _ _ _ _ (by rw [execInsn_addSub_reg_flags, writeFlags_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_snd_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_snd_snd]) hNT
  · exact conditionHolds_addSub _ _ _ _ (by rw [execInsn_addSub_reg_flags, writeFlags_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_snd_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_snd_snd]) hNT
  · exact conditionHolds_addSub _ _ _ _ (by rw [execInsn_addSub_reg_flags, writeFlags_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_snd_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_snd_snd]) hNT
  · simp [isTest] at hNT
  · exact conditionHolds_addSub _ _ _ _ (by rw [execInsn_addSub_reg_flags, writeFlags_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_snd_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_snd_snd]) hNT
  · exact conditionHolds_addSub _ _ _ _ (by rw [execInsn_addSub_reg_flags, writeFlags_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_snd_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_snd_snd]) hNT
  · exact conditionHolds_addSub _ _ _ _ (by rw [execInsn_addSub_reg_flags, writeFlags_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_snd_fst])
      (by rw [execInsn_addSub_reg_flags, writeFlags_snd_snd_snd]) hNT
  · simp [isTest] at hNT

/-- The condition code after the flag-setting `AND` with a register immediate. -/
theorem conditionHolds_and_imm (s : Arm8State) (cmp : Cmp) (r : Nat) (w : BitVec 64)
    (hT : isTest cmp = true) :
    conditionHolds (execInsn { s with pc := s.pc + 4 }
        (.logicalImmediate .and true w r 31)) (cmpCond cmp)
      = wordCmpHOL cmp (readReg s r) w := by
  cases cmp
  · simp [isTest] at hT
  · simp [isTest] at hT
  · simp [isTest] at hT
  · exact conditionHolds_test _ _ _ (execInsn_and_imm_z s r w)
  · simp [isTest] at hT
  · simp [isTest] at hT
  · simp [isTest] at hT
  · exact conditionHolds_notTest _ _ _ (execInsn_and_imm_z s r w)

/-- The condition code after the flag-setting `SUB` with a register immediate. -/
theorem conditionHolds_addSub_imm (s : Arm8State) (cmp : Cmp) (r : Nat) (w : BitVec 64)
    (hNT : isTest cmp = false) :
    conditionHolds (execInsn { s with pc := s.pc + 4 }
        (.addSubImmediate true true w r 31)) (cmpCond cmp)
      = wordCmpHOL cmp (readReg s r) w := by
  cases cmp
  · exact conditionHolds_addSub _ _ _ _ (by rw [execInsn_addSub_imm_flags, writeFlags_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_snd_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_snd_snd]) hNT
  · exact conditionHolds_addSub _ _ _ _ (by rw [execInsn_addSub_imm_flags, writeFlags_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_snd_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_snd_snd]) hNT
  · exact conditionHolds_addSub _ _ _ _ (by rw [execInsn_addSub_imm_flags, writeFlags_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_snd_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_snd_snd]) hNT
  · simp [isTest] at hNT
  · exact conditionHolds_addSub _ _ _ _ (by rw [execInsn_addSub_imm_flags, writeFlags_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_snd_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_snd_snd]) hNT
  · exact conditionHolds_addSub _ _ _ _ (by rw [execInsn_addSub_imm_flags, writeFlags_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_snd_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_snd_snd]) hNT
  · exact conditionHolds_addSub _ _ _ _ (by rw [execInsn_addSub_imm_flags, writeFlags_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_snd_fst])
      (by rw [execInsn_addSub_imm_flags, writeFlags_snd_snd_snd]) hNT
  · simp [isTest] at hNT

/-! ## Executing the second instruction -/

/-- A taken `branchConditional` moves the PC to `pc - 4 + imm`. -/
theorem execInsn_branchConditional_taken (s : Arm8State) (imm : W) (cond : Nat)
    (h : conditionHolds s cond = true) :
    execInsn s (.branchConditional imm cond) = { s with pc := s.pc - 4 + imm } := by
  simp only [execInsn, h, ite_true]

/-- An untaken `branchConditional` leaves the state (and the advanced PC) alone. -/
theorem execInsn_branchConditional_untaken (s : Arm8State) (imm : W) (cond : Nat)
    (h : conditionHolds s cond = false) :
    execInsn s (.branchConditional imm cond) = s := by
  simp [execInsn, h]

/-- The `i`-th word of a two-instruction encoding, for `i < 2`. -/
theorem mem_allPcs_two (p : BitVec 64) (i : Nat) (hi : i < 2) :
    p + BitVec.ofNat 64 (i * 4) ∈ allPcs 8 p 2 := by
  rw [allPcs_eq]
  exact ⟨i, by omega, by rw [show i * 2 ^ 2 = i * 4 by norm_num]⟩

/-- `arm8_enc` of a comparison branch is two four-byte instructions. -/
theorem arm8Enc_jumpCmp_length (cmp : Cmp) (r : Nat) (ri : HolRegImm 64) (a : BitVec 64) :
    (arm8Enc (.jumpCmp cmp r ri a)).length = 8 := by
  cases ri <;> simp [arm8Enc, arm8Ast, encodeBytes_length]

/-! ## The comparison-branch case -/

/-- The taken branch of a comparison at `pc + 4` lands at `pc + a`. -/
theorem jumpCmp_pc_taken (x a : BitVec 64) : x + 4 + 4 - 4 + (a - 4) = x + a := by
  bv_omega

/-- Unrolling two `arm8Next` steps. -/
theorem arm8Next_two (s : Arm8State) : arm8Next^[2] s = arm8Next (arm8Next s) := by
  rw [show 2 = Nat.succ 1 from rfl, Function.iterate_succ_apply', Function.iterate_one]

/-- The remaining work of a comparison branch once the flag-setting instruction
has been identified: the run is `t1` (the state after that instruction) and then
the conditional branch `branchConditional (a - 4) (cmpCond cmp)`, whose
condition is the source comparison. -/
theorem jumpCmpCase (cmp : Cmp) (r : Nat) (ri : HolRegImm 64) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms t1 : Arm8State)
    (h : asmStep arm8Config s1 (.jumpCmp cmp r ri a) s2 ∧ targetStateRel arm8Target s1 ms)
    (hlen : (arm8Enc (.jumpCmp cmp r ri a)).length = 8)
    (hnext1 : arm8Next ms = t1)
    (ht1pc : t1.pc = ms.pc + 4)
    (ht1mem : ∀ x, t1.mem x = ms.mem x)
    (ht1regs : ∀ i, t1.regs i = ms.regs i)
    (ht1failed : t1.failed = false)
    (ht1al : holAligned 2 t1.pc = true)
    (hcond : conditionHolds t1 (cmpCond cmp) = wordCmpHOL cmp (s1.regs r) (regImm ri s1))
    (hsafe0 : StepSafe s1.memDomain ms)
    (hb2 : bytesInMemoryHOL (ms.pc + 4)
      (encodeBytes (.branchConditional (a - 4) (cmpCond cmp))) ms.mem s1.memDomain) :
    CaseGoal (.jumpCmp cmp r ri a) s1 s2 ms := by
  have st := arm8Start (.jumpCmp cmp r ri a) s1 s2 ms h
  have hok := st.asmOk
  simp only [asmOkExact, Bool.and_eq_true] at hok
  obtain ⟨hfits, hmod⟩ := jumpCmp_cjumpOk_of_asm a hok.1
  have hb2' : bytesInMemoryHOL t1.pc
      (encodeBytes (.branchConditional (a - 4) (cmpCond cmp))) t1.mem s1.memDomain := by
    rw [ht1pc, show t1.mem = ms.mem from funext ht1mem]
    exact hb2
  have hstep2 : arm8Next t1 = execInsn { t1 with pc := t1.pc + 4 }
      (.branchConditional (a - 4) (cmpCond cmp)) :=
    arm8Next_branchConditional t1 s1.memDomain (a - 4) (cmpCond cmp) hfits hmod
      (cmpCond_lt cmp) hb2'
  have hfetch2 : fetchWord t1 =
      ((fields [(8, 84), (19, ((a - 4) >>> 2).toNat % 2 ^ 19), (1, 0),
        (4, cmpCond cmp)]).setWidth 64).setWidth 32 :=
    fetchWord_encodeBytes t1 (.branchConditional (a - 4) (cmpCond cmp)) _ s1.memDomain
      (encodeInsn_branchConditional (a - 4) (cmpCond cmp) hfits hmod) hb2'
  have hdec2 : decodeInsn32 (fetchWord t1) =
      some (.branchConditional (a - 4) (cmpCond cmp)) := by
    rw [hfetch2]
    show decodeInsn ((fields [(8, 84), (19, ((a - 4) >>> 2).toNat % 2 ^ 19), (1, 0),
      (4, cmpCond cmp)]).setWidth 64) = some (.branchConditional (a - 4) (cmpCond cmp))
    exact decode_encode_branchConditional (a - 4) (cmpCond cmp) hfits hmod (cmpCond_lt cmp)
  have hsafe1 : StepSafe s1.memDomain t1 := by
    have hdom := bytesInMemoryHOL_domain hb2'
    have hlen4 : (encodeBytes (.branchConditional (a - 4) (cmpCond cmp))).length = 4 :=
      encodeBytes_length _
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [arm8FetchBytes, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · simpa using hdom 0 (by rw [hlen4]; omega)
      · simpa using hdom 1 (by rw [hlen4]; omega)
      · simpa using hdom 2 (by rw [hlen4]; omega)
      · simpa using hdom 3 (by rw [hlen4]; omega)
    · intro i hi x hx
      rw [hdec2] at hi
      cases hi
      simp [arm8Touched] at hx
  have ht1ok : arm8StateOk t1 = true := arm8StateOk_set t1 ht1al ht1failed
  have hcond4 : conditionHolds { t1 with pc := t1.pc + 4 } (cmpCond cmp) =
      wordCmpHOL cmp (AsmSem.readReg r s1) (regImm ri s1) := hcond
  have hs2 : asmUpd (.jumpCmp cmp r ri a) (s1.pc + BitVec.ofNat 64 8) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2' : (if wordCmpHOL cmp (AsmSem.readReg r s1) (regImm ri s1) then jumpToOffset a s1
      else updPc (s1.pc + BitVec.ofNat 64 8) s1) = s2 := by
    simpa only [asmUpd] using hs2
  have hcode : allPcs (arm8Target.config.encode (.jumpCmp cmp r ri a)).length s1.pc 0 ⊆
      s1.memDomain := by
    rw [arm8Target_config, arm8Config_encode, ← st.pc]
    exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
  have hpc_untaken : holAligned 2 (ms.pc + 8) = true := by
    have h4 : holAligned 2 (4 : BitVec 64) = true := by
      rw [holAligned_iff]; decide
    have h1 : holAligned 2 (ms.pc + 4) = holAligned 2 ms.pc := (alignedAddSub 2 ms.pc 4 h4).1
    have h2 : holAligned 2 (ms.pc + 4 + 4) = holAligned 2 (ms.pc + 4) :=
      (alignedAddSub 2 (ms.pc + 4) 4 h4).1
    rw [show ms.pc + 8 = ms.pc + 4 + 4 by bv_omega, h2, h1, st.aligned]
  have hal4 : holAligned 2 (a - 4) = true := aligned_of_mod (a - 4) hmod
  have h4 : holAligned 2 (4 : BitVec 64) = true := by
    rw [holAligned_iff]; decide
  have haa : holAligned 2 a = true := by
    rw [show a = (a - 4) + 4 by bv_omega]
    rw [(alignedAddSub 2 (a - 4) 4 h4).1]
    exact hal4
  have hpc_taken : holAligned 2 (ms.pc + a) = true := by
    rw [(alignedAddSub 2 ms.pc a haa).1, st.aligned]
  by_cases hwc : wordCmpHOL cmp (AsmSem.readReg r s1) (regImm ri s1) = true
  · -- taken: the branch jumps to `s1.pc + a`
    rw [ite_eq_left hwc] at hs2'
    have hs2pc : s2.pc = s1.pc + a := by rw [← hs2']; rfl
    have hs2mem : ∀ x, s2.mem x = s1.mem x := by rw [← hs2']; intro x; rfl
    have hs2dom : s2.memDomain = s1.memDomain := by rw [← hs2']; rfl
    have hs2regs : ∀ i, s2.regs i = s1.regs i := by rw [← hs2']; intro i; rfl
    have hcondT : conditionHolds { t1 with pc := t1.pc + 4 } (cmpCond cmp) = true := by
      rw [hcond4, hwc]
    have hpcT : (t1.pc + 4) - 4 + (a - 4) = ms.pc + a := by
      rw [ht1pc]
      exact jumpCmp_pc_taken _ _
    have hnextT : arm8Next t1 = { t1 with pc := ms.pc + a } := by
      rw [hstep2, execInsn_branchConditional_taken _ _ _ hcondT, hpcT]
    have hpcm : t1.pc ∈ allPcs 8 s1.pc 2 := by
      have heq : t1.pc = s1.pc + BitVec.ofNat 64 (1 * 4) := by
        rw [ht1pc, st.pc]
        bv_omega
      rw [heq]
      exact mem_allPcs_two s1.pc 1 (by norm_num)
    have hq : targetStateRel arm8Target s2 (arm8Next^[2] ms) := by
      have hi : arm8Next^[2] ms = arm8Next t1 := by rw [arm8Next_two, hnext1]
      rw [hi, hnextT]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [arm8Target_stateOk]
        exact arm8StateOk_set _ hpc_taken ht1failed
      · show ms.pc + a = s2.pc
        rw [hs2pc, st.pc]
      · intro x hx
        show t1.mem x = s2.mem x
        rw [ht1mem x, hs2mem x]
        exact st.mem x (hs2dom ▸ hx)
      · intro i hi'
        show t1.regs i = s2.regs i
        rw [ht1regs i, hs2regs i]
        exact st.reg i hi'
      · intro i hi'
        simp only [arm8Target_config, arm8Config] at hi'
        omega
    refine encoderCaseStep (.jumpCmp cmp r ri a) s1 s2 ms 1 hs2dom hcode ?_ ?_ hq
    · intro k hk
      interval_cases k
      · simpa using hsafe0
      · rw [Function.iterate_one, hnext1]; exact hsafe1
    · intro k h1 h2
      have hk : k = 1 := by omega
      subst hk
      rw [Function.iterate_one, hnext1]
      refine ⟨ht1ok, fun pc _ => ht1mem pc, ?_⟩
      rw [arm8Target_config, arm8Config_encode, hlen]
      exact hpcm
  · -- untaken: the branch falls through to `s1.pc + 8`
    rw [ite_eq_right hwc] at hs2'
    have hs2pc : s2.pc = s1.pc + 8 := by rw [← hs2']; rfl
    have hs2mem : ∀ x, s2.mem x = s1.mem x := by rw [← hs2']; intro x; rfl
    have hs2dom : s2.memDomain = s1.memDomain := by rw [← hs2']; rfl
    have hs2regs : ∀ i, s2.regs i = s1.regs i := by rw [← hs2']; intro i; rfl
    have hcondU : conditionHolds { t1 with pc := t1.pc + 4 } (cmpCond cmp) = false := by
      rw [hcond4]; exact boolOfNotTrue hwc
    have hpcU : t1.pc + 4 = ms.pc + 8 := by
      rw [ht1pc]
      bv_omega
    have hnextU : arm8Next t1 = { t1 with pc := ms.pc + 8 } := by
      rw [hstep2, execInsn_branchConditional_untaken _ _ _ hcondU, hpcU]
    have hpcm : t1.pc ∈ allPcs 8 s1.pc 2 := by
      have heq : t1.pc = s1.pc + BitVec.ofNat 64 (1 * 4) := by
        rw [ht1pc, st.pc]
        bv_omega
      rw [heq]
      exact mem_allPcs_two s1.pc 1 (by norm_num)
    have hq : targetStateRel arm8Target s2 (arm8Next^[2] ms) := by
      have hi : arm8Next^[2] ms = arm8Next t1 := by rw [arm8Next_two, hnext1]
      rw [hi, hnextU]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [arm8Target_stateOk]
        exact arm8StateOk_set _ hpc_untaken ht1failed
      · show ms.pc + 8 = s2.pc
        rw [hs2pc, st.pc]
      · intro x hx
        show t1.mem x = s2.mem x
        rw [ht1mem x, hs2mem x]
        exact st.mem x (hs2dom ▸ hx)
      · intro i hi'
        show t1.regs i = s2.regs i
        rw [ht1regs i, hs2regs i]
        exact st.reg i hi'
      · intro i hi'
        simp only [arm8Target_config, arm8Config] at hi'
        omega
    refine encoderCaseStep (.jumpCmp cmp r ri a) s1 s2 ms 1 hs2dom hcode ?_ ?_ hq
    · intro k hk
      interval_cases k
      · simpa using hsafe0
      · rw [Function.iterate_one, hnext1]; exact hsafe1
    · intro k h1 h2
      have hk : k = 1 := by omega
      subst hk
      rw [Function.iterate_one, hnext1]
      refine ⟨ht1ok, fun pc _ => ht1mem pc, ?_⟩
      rw [arm8Target_config, arm8Config_encode, hlen]
      exact hpcm


/-! ## Immediate side conditions -/

/-- `4` is four-byte aligned. -/
theorem holAligned_four : holAligned 2 (4 : BitVec 64) = true := by
  rw [holAligned_iff]; decide

/-- The `-1` special case of `asmRegImmOkExact` never applies to a comparison
operator. -/
theorem and_beq_xor_eq_false (cmp : Cmp) (w : BitVec 64) :
    ((Sum.inr cmp == (Sum.inl .xor : Sum BinOp Cmp)) && (w == -1)) = false := by
  cases cmp <;> rfl

/-- The immediate side condition `asm_ok` leaves for a comparison. -/
theorem validImmediate_of_asmRegImm {cmp : Cmp} {w : BitVec 64}
    (h : asmRegImmOkExact (.inr cmp) (.imm w) arm8Config = true) :
    validImmediate (.inr cmp) w = true := by
  have h2 : (((Sum.inr cmp == (Sum.inl .xor : Sum BinOp Cmp)) && (w == -1)) ||
      arm8Config.validImm (.inr cmp) w) = true := h
  rw [and_beq_xor_eq_false cmp w, Bool.false_or] at h2
  exact h2

/-- The `validImmediate` test of a `test`/`notTest` comparison is the bitmask
encoder test. -/
theorem validImmediate_test {cmp : Cmp} (hT : isTest cmp = true) {w : BitVec 64}
    (h : validImmediate (.inr cmp) w = true) : (encodeBitMask w).isSome = true := by
  cases cmp
  case equal => simp [isTest] at hT
  case lower => simp [isTest] at hT
  case less => simp [isTest] at hT
  case test => simpa only [validImmediate] using h
  case notEqual => simp [isTest] at hT
  case notLower => simp [isTest] at hT
  case notLess => simp [isTest] at hT
  case notTest => simpa only [validImmediate] using h

/-- The `validImmediate` test of a non-`test` comparison is the twelve-bit range
test. -/
theorem validImmediate_notTest {cmp : Cmp} (hNT : isTest cmp = false) {w : BitVec 64}
    (h : validImmediate (.inr cmp) w = true) :
    w &&& ~~~(0xFFF : BitVec 64) = 0 ∨ w &&& ~~~(0xFFF000 : BitVec 64) = 0 := by
  cases cmp
  case equal => simpa only [validImmediate, Bool.or_eq_true, decide_eq_true_eq] using h
  case lower => simpa only [validImmediate, Bool.or_eq_true, decide_eq_true_eq] using h
  case less => simpa only [validImmediate, Bool.or_eq_true, decide_eq_true_eq] using h
  case test => simp [isTest] at hNT
  case notEqual => simpa only [validImmediate, Bool.or_eq_true, decide_eq_true_eq] using h
  case notLower => simpa only [validImmediate, Bool.or_eq_true, decide_eq_true_eq] using h
  case notLess => simpa only [validImmediate, Bool.or_eq_true, decide_eq_true_eq] using h
  case notTest => simp [isTest] at hNT

/-- A word killed by the shifted mask is a multiple of `4096` below `2 ^ 24`, so
it is `m <<< 12` for the twelve-bit value `m` the shifted encoding needs. -/
theorem jumpCmp_ofNat_shifted (w : BitVec 64) (hmod : w.toNat % 4096 = 0)
    (hlt : w.toNat < 2 ^ 24) :
    BitVec.ofNat 64 (((w >>> 12).toNat % 4096) <<< 12) = w := by
  have hshift : (w >>> 12).toNat = w.toNat / 4096 := by
    rw [show (w >>> 12).toNat = w.toNat >>> 12 from BitVec.toNat_ushiftRight w 12,
      Nat.shiftRight_eq_div_pow]
  have hquo : w.toNat / 4096 % 4096 = w.toNat / 4096 := by
    apply Nat.mod_eq_of_lt
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, hshift, hquo, Nat.shiftLeft_eq]
  have hdvd : 4096 ∣ w.toNat := Nat.dvd_of_mod_eq_zero hmod
  rw [show (2 : Nat) ^ 12 = 4096 from rfl, Nat.div_mul_cancel hdvd]
  exact Nat.mod_eq_of_lt w.isLt

/-! ## The two `CaseGoal` theorems -/

/-- The `jumpCmp` case with a register operand: the `JumpCmp`/`INR (INL ...)`
branch of HOL `arm8_encoder_correct`. -/
theorem case_jumpCmp_reg (cmp : Cmp) (r : Nat) (u : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.jumpCmp cmp r (.reg u) a) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.jumpCmp cmp r (.reg u) a) s1 s2 ms := by
  have st := arm8Start (.jumpCmp cmp r (.reg u) a) s1 s2 ms h
  have hok : asmCjumpOffsetOkExact arm8Config a = true ∧ asmRegOkExact r arm8Config = true ∧
      asmRegOkExact u arm8Config = true := by
    have h' := st.asmOk
    rw [show asmOkExact (.jumpCmp cmp r (.reg u) a) arm8Config =
        (asmCjumpOffsetOkExact arm8Config a &&
          (asmRegOkExact r arm8Config && asmRegOkExact u arm8Config)) from rfl] at h'
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h'
    obtain ⟨h3, h4⟩ := Bool.and_eq_true_iff.mp h2
    exact ⟨h1, h3, h4⟩
  obtain ⟨hlt, hav, hne31⟩ := regOk_of_asm hok.2.1
  obtain ⟨hltu, havu, hneu31⟩ := regOk_of_asm hok.2.2
  have hlen := arm8Enc_jumpCmp_length cmp r (.reg u) a
  have hb := st.bytes
  simp only [arm8Enc, arm8Ast] at hb
  rw [bytesInMemory_cons, bytesInMemory_one] at hb
  obtain ⟨hb1, hb2⟩ := hb
  have hr : readReg ms r = s1.regs r := by
    simp only [readReg, ite_eq_right hne31]
    exact st.reg r ⟨hlt, hav⟩
  have hu : readReg ms u = s1.regs u := by
    simp only [readReg, ite_eq_right hneu31]
    exact st.reg u ⟨hltu, havu⟩
  by_cases hT : isTest cmp = true
  · -- `test`/`notTest`: `AND` of the two registers
    rw [ite_eq_left hT] at hb1
    have hsafe0 : StepSafe s1.memDomain ms :=
      stepSafe_of_encode ms s1.memDomain _ _ hb1
        (encodeInsn_logicalShiftedRegister .and false true .lsl 0 u r 31 3 (by decide)
          (by decide))
        (decode_encode_logicalShiftedRegister .and false true .lsl 0 u r 31 3 (by decide)
          (by decide) hltu hlt (by decide))
        (by rfl)
    let t1 : Arm8State := execInsn { ms with pc := ms.pc + 4 }
      (.logicalShiftedRegister .and false true .lsl 0 u r 31)
    have hnext1 : arm8Next ms = t1 :=
      arm8Next_logicalShiftedRegister ms s1.memDomain .and false true .lsl 0 u r 31 3
        (by decide) (by decide) hltu hlt (by decide) hb1
    have ht1pc : t1.pc = ms.pc + 4 := rfl
    have ht1mem : ∀ x, t1.mem x = ms.mem x := fun _ => rfl
    have ht1regs : ∀ i, t1.regs i = ms.regs i := fun _ => rfl
    have ht1failed : t1.failed = false := st.msFailed
    have ht1al : holAligned 2 t1.pc = true := by
      rw [ht1pc, (alignedAddSub 2 ms.pc 4 holAligned_four).1, st.aligned]
    have hcond : conditionHolds t1 (cmpCond cmp) =
        wordCmpHOL cmp (s1.regs r) (regImm (.reg u) s1) := by
      have hc := conditionHolds_and_reg ms cmp r u hT
      rw [hr, hu] at hc
      exact hc
    exact jumpCmpCase cmp r (.reg u) a s1 s2 ms t1 h hlen hnext1 ht1pc ht1mem ht1regs
      ht1failed ht1al hcond hsafe0 hb2
  · -- a non-`test` comparison: `SUB` of the two registers
    have hNT : isTest cmp = false := boolOfNotTrue hT
    rw [ite_eq_right hT] at hb1
    have hsafe0 : StepSafe s1.memDomain ms :=
      stepSafe_of_encode ms s1.memDomain _ _ hb1
        (encodeInsn_addSubShiftedRegister true true .lsl u 0 r 31)
        (decode_encode_addSubShiftedRegisterInsn true true .lsl u 0 r 31 hltu (by decide)
          hlt (by decide))
        (by rfl)
    let t1 : Arm8State := execInsn { ms with pc := ms.pc + 4 }
      (.addSubShiftedRegister true true .lsl u 0 r 31)
    have hnext1 : arm8Next ms = t1 :=
      arm8Next_addSubShiftedRegister ms s1.memDomain true true .lsl u 0 r 31 hltu (by decide)
        hlt (by decide) hb1
    have ht1pc : t1.pc = ms.pc + 4 := rfl
    have ht1mem : ∀ x, t1.mem x = ms.mem x := fun _ => rfl
    have ht1regs : ∀ i, t1.regs i = ms.regs i := fun _ => rfl
    have ht1failed : t1.failed = false := st.msFailed
    have ht1al : holAligned 2 t1.pc = true := by
      rw [ht1pc, (alignedAddSub 2 ms.pc 4 holAligned_four).1, st.aligned]
    have hcond : conditionHolds t1 (cmpCond cmp) =
        wordCmpHOL cmp (s1.regs r) (regImm (.reg u) s1) := by
      have hc := conditionHolds_addSub_reg ms cmp r u hNT
      rw [hr, hu] at hc
      exact hc
    exact jumpCmpCase cmp r (.reg u) a s1 s2 ms t1 h hlen hnext1 ht1pc ht1mem ht1regs
      ht1failed ht1al hcond hsafe0 hb2

/-- The `jumpCmp` case with an immediate operand: the `JumpCmp`/`INR (INR ...)`
branch of HOL `arm8_encoder_correct`, whose informative side condition is the
`valid_immediate` test of `arm8Config`. -/
theorem case_jumpCmp_imm (cmp : Cmp) (r : Nat) (w : BitVec 64) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.jumpCmp cmp r (.imm w) a) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.jumpCmp cmp r (.imm w) a) s1 s2 ms := by
  have st := arm8Start (.jumpCmp cmp r (.imm w) a) s1 s2 ms h
  have hok : asmCjumpOffsetOkExact arm8Config a = true ∧ asmRegOkExact r arm8Config = true ∧
      asmRegImmOkExact (.inr cmp) (.imm w) arm8Config = true := by
    have h' := st.asmOk
    rw [show asmOkExact (.jumpCmp cmp r (.imm w) a) arm8Config =
        (asmCjumpOffsetOkExact arm8Config a &&
          (asmRegOkExact r arm8Config && asmRegImmOkExact (.inr cmp) (.imm w) arm8Config))
        from rfl] at h'
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h'
    obtain ⟨h3, h4⟩ := Bool.and_eq_true_iff.mp h2
    exact ⟨h1, h3, h4⟩
  obtain ⟨hlt, hav, hne31⟩ := regOk_of_asm hok.2.1
  have hv : validImmediate (.inr cmp) w = true := validImmediate_of_asmRegImm hok.2.2
  have hlen := arm8Enc_jumpCmp_length cmp r (.imm w) a
  have hb := st.bytes
  simp only [arm8Enc, arm8Ast] at hb
  rw [bytesInMemory_cons, bytesInMemory_one] at hb
  obtain ⟨hb1, hb2⟩ := hb
  have hr : readReg ms r = s1.regs r := by
    simp only [readReg, ite_eq_right hne31]
    exact st.reg r ⟨hlt, hav⟩
  by_cases hT : isTest cmp = true
  · -- `test`/`notTest`: `AND` with an encodable bitmask
    rw [ite_eq_left hT] at hb1
    have hisSome : (encodeBitMask w).isSome = true := validImmediate_test hT hv
    obtain ⟨⟨n, imms, immr⟩, hbm⟩ := Option.isSome_iff_exists.mp hisSome
    have hsafe0 : StepSafe s1.memDomain ms :=
      stepSafe_of_encode ms s1.memDomain _ _ hb1
        (encodeInsn_logicalImmediate .and true w r 31 3 n imms immr (by decide) hbm)
        (decode_encode_logicalImmediate .and true w r 31 3 n imms immr (by decide) hbm
          hlt (by decide))
        (by rfl)
    let t1 : Arm8State := execInsn { ms with pc := ms.pc + 4 }
      (.logicalImmediate .and true w r 31)
    have hnext1 : arm8Next ms = t1 :=
      arm8Next_logicalImmediate ms s1.memDomain .and true w r 31 3 n imms immr (by decide)
        hbm hlt (by decide) hb1
    have ht1pc : t1.pc = ms.pc + 4 := rfl
    have ht1mem : ∀ x, t1.mem x = ms.mem x := fun _ => rfl
    have ht1regs : ∀ i, t1.regs i = ms.regs i := fun _ => rfl
    have ht1failed : t1.failed = false := st.msFailed
    have ht1al : holAligned 2 t1.pc = true := by
      rw [ht1pc, (alignedAddSub 2 ms.pc 4 holAligned_four).1, st.aligned]
    have hcond : conditionHolds t1 (cmpCond cmp) =
        wordCmpHOL cmp (s1.regs r) (regImm (.imm w) s1) := by
      have hc := conditionHolds_and_imm ms cmp r w hT
      rw [hr] at hc
      exact hc
    exact jumpCmpCase cmp r (.imm w) a s1 s2 ms t1 h hlen hnext1 ht1pc ht1mem ht1regs
      ht1failed ht1al hcond hsafe0 hb2
  · -- a non-`test` comparison: `SUB` with a twelve-bit immediate
    have hNT : isTest cmp = false := boolOfNotTrue hT
    rw [ite_eq_right hT] at hb1
    have hdisj := validImmediate_notTest hNT hv
    by_cases hlow : w &&& ~~~(0xFFF : BitVec 64) = 0
    · -- the unshifted form
      have hwlt : w.toNat < 4096 := and_not_fff_eq_zero_toNat_lt hlow
      have hsafe0 : StepSafe s1.memDomain ms :=
        stepSafe_of_encode ms s1.memDomain _ _ hb1
          (encodeInsn_addSubImmediate true true w r 31 hwlt)
          (decode_encode_addSubImmediate true true w r 31 hwlt hlt (by decide)) (by rfl)
      let t1 : Arm8State := execInsn { ms with pc := ms.pc + 4 }
        (.addSubImmediate true true w r 31)
      have hnext1 : arm8Next ms = t1 :=
        arm8Next_addSubImmediate ms s1.memDomain true true w r 31 hwlt hlt (by decide) hb1
      have ht1pc : t1.pc = ms.pc + 4 := rfl
      have ht1mem : ∀ x, t1.mem x = ms.mem x := fun _ => rfl
      have ht1regs : ∀ i, t1.regs i = ms.regs i := fun _ => rfl
      have ht1failed : t1.failed = false := st.msFailed
      have ht1al : holAligned 2 t1.pc = true := by
        rw [ht1pc, (alignedAddSub 2 ms.pc 4 holAligned_four).1, st.aligned]
      have hcond : conditionHolds t1 (cmpCond cmp) =
          wordCmpHOL cmp (s1.regs r) (regImm (.imm w) s1) := by
        have hc := conditionHolds_addSub_imm ms cmp r w hNT
        rw [hr] at hc
        exact hc
      exact jumpCmpCase cmp r (.imm w) a s1 s2 ms t1 h hlen hnext1 ht1pc ht1mem ht1regs
        ht1failed ht1al hcond hsafe0 hb2
    · -- the shifted form `w = m <<< 12`
      have hhigh : w &&& ~~~(0xFFF000 : BitVec 64) = 0 := by
        rcases hdisj with h | h
        · exact absurd h hlow
        · exact h
      have hmod : w.toNat % 4096 = 0 := and_not_fff000_eq_zero_toNat_mod hhigh
      have hlt24 : w.toNat < 2 ^ 24 := and_not_fff000_eq_zero_toNat_lt hhigh
      have hweq : BitVec.ofNat 64 (((w >>> 12).toNat % 4096) <<< 12) = w :=
        jumpCmp_ofNat_shifted w hmod hlt24
      have hm : ((w >>> 12).toNat % 4096) < 4096 := Nat.mod_lt _ (by decide)
      have hm0 : ((w >>> 12).toNat % 4096) ≠ 0 := by
        intro h0
        apply hlow
        rw [← hweq, h0]
        simp
      have hb1' : bytesInMemoryHOL ms.pc
          (encodeBytes (.addSubImmediate true true
            (BitVec.ofNat 64 (((w >>> 12).toNat % 4096) <<< 12)) r 31))
          ms.mem s1.memDomain := by
        rw [hweq]
        exact hb1
      have hsafe0 : StepSafe s1.memDomain ms :=
        stepSafe_of_encode ms s1.memDomain _ _ hb1'
          (encodeInsn_addSubImmediateShifted true true _ r 31 hm hm0)
          (decode_encode_addSubImmediateShifted true true _ r 31 hm hlt (by decide)) (by rfl)
      have hnext1 : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
          (.addSubImmediate true true w r 31) := by
        have h' := arm8Next_addSubImmediateShifted ms s1.memDomain true true
          ((w >>> 12).toNat % 4096) r 31 hm hm0 hlt (by decide) hb1'
        rw [hweq] at h'
        exact h'
      let t1 : Arm8State := execInsn { ms with pc := ms.pc + 4 }
        (.addSubImmediate true true w r 31)
      have ht1pc : t1.pc = ms.pc + 4 := rfl
      have ht1mem : ∀ x, t1.mem x = ms.mem x := fun _ => rfl
      have ht1regs : ∀ i, t1.regs i = ms.regs i := fun _ => rfl
      have ht1failed : t1.failed = false := st.msFailed
      have ht1al : holAligned 2 t1.pc = true := by
        rw [ht1pc, (alignedAddSub 2 ms.pc 4 holAligned_four).1, st.aligned]
      have hcond : conditionHolds t1 (cmpCond cmp) =
          wordCmpHOL cmp (s1.regs r) (regImm (.imm w) s1) := by
        have hc := conditionHolds_addSub_imm ms cmp r w hNT
        rw [hr] at hc
        exact hc
      exact jumpCmpCase cmp r (.imm w) a s1 s2 ms t1 h hlen hnext1 ht1pc ht1mem ht1regs
        ht1failed ht1al hcond hsafe0 hb2

end Flapjack.Compiler.Encoders.Arm8
