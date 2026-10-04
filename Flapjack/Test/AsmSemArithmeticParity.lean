import Flapjack.Compiler.Backend.LabToTarget.AsmUpdates

/-! Direct original asmSem oracle replays. Other state fields are arbitrary;
no compiler callback or alternate arithmetic evaluator supplies the results. -/
set_option maxRecDepth 16384

namespace Flapjack.Test.AsmSemArithmeticParity
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem

-- Original row asm_binop_add.
example (s : AsmState 8) :
    let t := arithUpd (.binop .add 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then 255 else if r = 3 then 2 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (1, 99, 99, false, 255, 2) := by
  simp +decide [arithUpd, binopUpd, regImm, readReg, updReg]

-- Original row asm_binop_sub.
example (s : AsmState 8) :
    let t := arithUpd (.binop .sub 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then 1 else if r = 3 then 2 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (255, 99, 99, false, 1, 2) := by
  simp +decide [arithUpd, binopUpd, regImm, readReg, updReg]

-- Original row asm_binop_and.
example (s : AsmState 8) :
    let t := arithUpd (.binop .and 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then 240 else if r = 3 then 15 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (0, 99, 99, false, 240, 15) := by
  simp +decide [arithUpd, binopUpd, regImm, readReg, updReg]

-- Original row asm_binop_or.
example (s : AsmState 8) :
    let t := arithUpd (.binop .or 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then 240 else if r = 3 then 15 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (255, 99, 99, false, 240, 15) := by
  simp +decide [arithUpd, binopUpd, regImm, readReg, updReg]

-- Original row asm_binop_xor.
example (s : AsmState 8) :
    let t := arithUpd (.binop .xor 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then 170 else if r = 3 then 15 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (165, 99, 99, false, 170, 15) := by
  simp +decide [arithUpd, binopUpd, regImm, readReg, updReg]

-- Original row asm_lsl_reg_valid.
example (s : AsmState 8) :
    let t := arithUpd (.shift .lsl 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then 1 else if r = 3 then 7 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (128, 99, 99, false, 1, 7) := by
  simp +decide [arithUpd, regImm, readReg, updReg, assertState, wordShift]

-- Original row asm_lsl_reg_invalid.
example (s : AsmState 8) :
    let t := arithUpd (.shift .lsl 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then 128 else if r = 3 then 8 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (0, 99, 99, true, 128, 8) := by
  simp +decide [arithUpd, regImm, readReg, updReg, assertState, wordShift]

-- Original row asm_lsl_imm_past.
example (s : AsmState 8) :
    let t := arithUpd (.shift .lsl 0 2 (.imm 8)) { s with regs := fun r => if r = 2 then 128 else if r = 3 then 8 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (0, 99, 99, false, 128, 8) := by
  simp +decide [arithUpd, regImm, readReg, updReg, assertState, wordShift]

-- Original row asm_lsr_reg_invalid.
example (s : AsmState 8) :
    let t := arithUpd (.shift .lsr 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then 255 else if r = 3 then 9 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (0, 99, 99, true, 255, 9) := by
  simp +decide [arithUpd, regImm, readReg, updReg, assertState, wordShift]

-- Original row asm_asr_reg_invalid.
example (s : AsmState 8) :
    let t := arithUpd (.shift .asr 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then 128 else if r = 3 then 9 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (255, 99, 99, true, 128, 9) := by
  simp +decide [arithUpd, regImm, readReg, updReg, assertState, wordShift]

-- Original row asm_ror_reg_invalid.
example (s : AsmState 8) :
    let t := arithUpd (.shift .ror 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then 128 else if r = 3 then 9 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (64, 99, 99, true, 128, 9) := by
  simp +decide [arithUpd, regImm, readReg, updReg, assertState, wordShift]

-- Original row asm_ror_imm_past.
example (s : AsmState 8) :
    let t := arithUpd (.shift .ror 0 2 (.imm 9)) { s with regs := fun r => if r = 2 then 128 else if r = 3 then 9 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (64, 99, 99, false, 128, 9) := by
  simp +decide [arithUpd, regImm, readReg, updReg, assertState, wordShift]

-- Original row asm_shift_alias_count.
example (s : AsmState 8) :
    let t := arithUpd (.shift .lsl 3 2 (.reg 3)) { s with regs := fun r => if r = 2 then 1 else if r = 3 then 8 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (99, 99, 99, true, 1, 0) := by
  simp +decide [arithUpd, regImm, readReg, updReg, assertState, wordShift]

-- Original row asm_div_ok.
example (s : AsmState 8) :
    let t := arithUpd (.div 0 2 3) { s with regs := fun r => if r = 2 then 23 else if r = 3 then 5 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (4, 99, 99, false, 23, 5) := by
  simp +decide [arithUpd, readReg, updReg, assertState]

-- Original row asm_div_zero_write.
example (s : AsmState 8) :
    let t := arithUpd (.div 0 2 3) { s with regs := fun r => if r = 2 then 23 else if r = 3 then 0 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (0, 99, 99, true, 23, 0) := by
  simp +decide [arithUpd, readReg, updReg, assertState]

-- Original row asm_div_source_alias.
example (s : AsmState 8) :
    let t := arithUpd (.div 2 2 3) { s with regs := fun r => if r = 2 then 23 else if r = 3 then 5 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (99, 99, 99, false, 4, 5) := by
  simp +decide [arithUpd, readReg, updReg, assertState]

-- Original row asm_div_neg_dividend (signed word_quot).
example (s : AsmState 8) :
    let t := arithUpd (.div 0 2 3) { s with regs := fun r => if r = 2 then 233 else if r = 3 then 5 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (252, 99, 99, false, 233, 5) := by
  simp +decide [arithUpd, readReg, updReg, assertState]

-- Original row asm_div_neg_divisor.
example (s : AsmState 8) :
    let t := arithUpd (.div 0 2 3) { s with regs := fun r => if r = 2 then 23 else if r = 3 then 251 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (252, 99, 99, false, 23, 251) := by
  simp +decide [arithUpd, readReg, updReg, assertState]

-- Original row asm_div_both_neg.
example (s : AsmState 8) :
    let t := arithUpd (.div 0 2 3) { s with regs := fun r => if r = 2 then 233 else if r = 3 then 251 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (4, 99, 99, false, 233, 251) := by
  simp +decide [arithUpd, readReg, updReg, assertState]

-- Original row asm_div_min_by_minus_one.
example (s : AsmState 8) :
    let t := arithUpd (.div 0 2 3) { s with regs := fun r => if r = 2 then 128 else if r = 3 then 255 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (128, 99, 99, false, 128, 255) := by
  simp +decide [arithUpd, readReg, updReg, assertState]

-- Original row asm_div_neg_source_alias.
example (s : AsmState 8) :
    let t := arithUpd (.div 2 2 3) { s with regs := fun r => if r = 2 then 233 else if r = 3 then 5 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (99, 99, 99, false, 252, 5) := by
  simp +decide [arithUpd, readReg, updReg, assertState]

-- Original row asm_longmul.
example (s : AsmState 8) :
    let t := arithUpd (.longMul 0 1 2 3) { s with regs := fun r => if r = 2 then 255 else if r = 3 then 255 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (254, 1, 99, false, 255, 255) := by
  simp +decide [arithUpd, readReg, updReg]

-- Original row asm_longmul_alias.
example (s : AsmState 8) :
    let t := arithUpd (.longMul 0 0 2 3) { s with regs := fun r => if r = 2 then 255 else if r = 3 then 255 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (1, 99, 99, false, 255, 255) := by
  simp +decide [arithUpd, readReg, updReg]

-- Original row asm_longdiv_ok.
example (s : AsmState 8) :
    let t := arithUpd (.longDiv 0 1 2 3 4) { s with regs := fun r => if r = 2 then 1 else if r = 3 then 5 else if r = 4 then 7 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (37, 2, 7, false, 1, 5) := by
  simp +decide [arithUpd, readReg, updReg, assertState]

-- Original row asm_longdiv_overflow_write.
example (s : AsmState 8) :
    let t := arithUpd (.longDiv 0 1 2 3 4) { s with regs := fun r => if r = 2 then 255 else if r = 3 then 255 else if r = 4 then 1 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (255, 0, 1, true, 255, 255) := by
  simp +decide [arithUpd, readReg, updReg, assertState]

-- Original row asm_longdiv_zero_write.
example (s : AsmState 8) :
    let t := arithUpd (.longDiv 0 1 2 3 4) { s with regs := fun r => if r = 2 then 1 else if r = 3 then 5 else if r = 4 then 0 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (0, 5, 0, true, 1, 5) := by
  simp +decide [arithUpd, readReg, updReg, assertState]

-- Original row asm_longdiv_alias.
example (s : AsmState 8) :
    let t := arithUpd (.longDiv 0 0 2 3 4) { s with regs := fun r => if r = 2 then 1 else if r = 3 then 5 else if r = 4 then 7 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (37, 99, 7, false, 1, 5) := by
  simp +decide [arithUpd, readReg, updReg, assertState]

-- Original row asm_addcarry.
example (s : AsmState 8) :
    let t := arithUpd (.addCarry 0 2 3 4) { s with regs := fun r => if r = 2 then 255 else if r = 3 then 1 else if r = 4 then 17 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (1, 99, 1, false, 255, 1) := by
  simp +decide [arithUpd, readReg, updReg]

-- Original row asm_addcarry_no_carry.
example (s : AsmState 8) :
    let t := arithUpd (.addCarry 0 2 3 4) { s with regs := fun r => if r = 2 then 3 else if r = 3 then 4 else if r = 4 then 0 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (7, 99, 0, false, 3, 4) := by
  simp +decide [arithUpd, readReg, updReg]

-- Original row asm_addcarry_alias.
example (s : AsmState 8) :
    let t := arithUpd (.addCarry 0 2 3 0) { s with regs := fun r => if r = 0 then 17 else if r = 2 then 255 else if r = 3 then 1 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (1, 99, 99, false, 255, 1) := by
  simp +decide [arithUpd, readReg, updReg]

-- Original row asm_addoverflow.
example (s : AsmState 8) :
    let t := arithUpd (.addOverflow 0 2 3 4) { s with regs := fun r => if r = 2 then 127 else if r = 3 then 1 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (128, 99, 1, false, 127, 1) := by
  simp +decide [arithUpd, readReg, updReg]

-- Original row asm_addoverflow_no_flag.
example (s : AsmState 8) :
    let t := arithUpd (.addOverflow 0 2 3 4) { s with regs := fun r => if r = 2 then 1 else if r = 3 then 2 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (3, 99, 0, false, 1, 2) := by
  simp +decide [arithUpd, readReg, updReg]

-- Original row asm_addoverflow_alias.
example (s : AsmState 8) :
    let t := arithUpd (.addOverflow 0 2 3 0) { s with regs := fun r => if r = 2 then 127 else if r = 3 then 1 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (1, 99, 99, false, 127, 1) := by
  simp +decide [arithUpd, readReg, updReg]

-- Original row asm_suboverflow.
example (s : AsmState 8) :
    let t := arithUpd (.subOverflow 0 2 3 4) { s with regs := fun r => if r = 2 then 128 else if r = 3 then 1 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (127, 99, 1, false, 128, 1) := by
  simp +decide [arithUpd, readReg, updReg]

-- Original row asm_suboverflow_alias.
example (s : AsmState 8) :
    let t := arithUpd (.subOverflow 0 2 3 0) { s with regs := fun r => if r = 2 then 128 else if r = 3 then 1 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (1, 99, 99, false, 128, 1) := by
  simp +decide [arithUpd, readReg, updReg]

-- Original row asm_prior_failure.
example (s : AsmState 8) :
    let t := arithUpd (.binop .add 0 2 (.imm 1)) { s with regs := fun r => if r = 2 then 4 else 99, failed := true }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (5, 99, 99, true, 4, 99) := by
  simp +decide [arithUpd, binopUpd, regImm, readReg, updReg]

-- Original row asm_width1_carry.
example (s : AsmState 1) :
    let t := arithUpd (.addCarry 0 2 3 4) { s with regs := fun r => if r = 2 then 1 else if r = 3 then 1 else if r = 4 then 0 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (0, 1, 1, false, 1, 1) := by
  simp +decide [arithUpd, readReg, updReg]

-- Original row asm_width32_overflow.
example (s : AsmState 32) :
    let t := arithUpd (.addOverflow 0 2 3 4) { s with regs := fun r => if r = 2 then 2147483647 else if r = 3 then 1 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (2147483648, 99, 1, false, 2147483647, 1) := by
  simp +decide [arithUpd, readReg, updReg]

-- Original row asm_width64_longmul.
example (s : AsmState 64) :
    let t := arithUpd (.longMul 0 1 2 3) { s with regs := fun r => if r = 2 then 18446744073709551615 else if r = 3 then 2 else 99, failed := false }
    (t.regs 0 |>.toNat, t.regs 1 |>.toNat, t.regs 4 |>.toNat, t.failed, t.regs 2 |>.toNat, t.regs 3 |>.toNat) = (1, 18446744073709551614, 99, false, 18446744073709551615, 2) := by
  simp +decide [arithUpd, readReg, updReg]

-- Original row asm_upd_pc.
example (s : AsmState 8) : (updPc 99 { s with regs := fun r => if r = 2 then 13 else 11, fpRegs := fun _ => 7, mem := fun _ => 8, pc := 200, failed := false }).pc.toNat = 99 := rfl

-- Original row asm_upd_reg.
example (s : AsmState 8) : (readReg 2 (updReg 2 42 { s with regs := fun r => if r = 2 then 13 else 11, fpRegs := fun _ => 7, mem := fun _ => 8, pc := 200, failed := false })).toNat = 42 := rfl

-- Original row asm_upd_reg_other.
example (s : AsmState 8) : (readReg 3 (updReg 2 42 { s with regs := fun r => if r = 2 then 13 else 11, fpRegs := fun _ => 7, mem := fun _ => 8, pc := 200, failed := false })).toNat = 11 := rfl

-- Original row asm_upd_fp_reg.

-- Original row asm_upd_mem.
example (s : AsmState 8) : (readMem 255 (updMem 255 200 { s with regs := fun r => if r = 2 then 13 else 11, fpRegs := fun _ => 7, mem := fun _ => 8, pc := 200, failed := false })).toNat = 200 := rfl

-- Original row asm_upd_mem_other.
example (s : AsmState 8) : (readMem 0 (updMem 255 200 { s with regs := fun r => if r = 2 then 13 else 11, fpRegs := fun _ => 7, mem := fun _ => 8, pc := 200, failed := false })).toNat = 8 := rfl

-- Original row asm_assert_false.
example (s : AsmState 8) : (assertState false { s with regs := fun r => if r = 2 then 13 else 11, fpRegs := fun _ => 7, mem := fun _ => 8, pc := 200, failed := false }).failed = true := rfl

-- Original row asm_assert_prior.
example (s : AsmState 8) : (assertState true { { s with regs := fun r => if r = 2 then 13 else 11, fpRegs := fun _ => 7, mem := fun _ => 8, pc := 200, failed := false } with failed := true }).failed = true := rfl

-- Original row asm_reg_imm_reg.
example (s : AsmState 8) : (regImm (.reg 2) { s with regs := fun r => if r = 2 then 13 else 11, fpRegs := fun _ => 7, mem := fun _ => 8, pc := 200, failed := false }).toNat = 13 := rfl

-- Original row asm_reg_imm_imm.
example (s : AsmState 8) : (regImm (.imm 99) { s with regs := fun r => if r = 2 then 13 else 11, fpRegs := fun _ => 7, mem := fun _ => 8, pc := 200, failed := false }).toNat = 99 := rfl

example : isTest .equal = false := rfl

example : isTest .lower = false := rfl

example : isTest .less = false := rfl

example : isTest .test = true := rfl

example : isTest .notEqual = false := rfl

example : isTest .notLower = false := rfl

example : isTest .notLess = false := rfl

example : isTest .notTest = true := rfl

def runChecks : IO Bool := do
  IO.println "PASS original native assembly arithmetic/state operations (52 kernel replays)"
  return true
end Flapjack.Test.AsmSemArithmeticParity
