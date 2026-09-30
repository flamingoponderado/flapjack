import Flapjack.Compiler.Backend.StackProps.ArithmeticNames
namespace Flapjack.Test.StackPropsArithmeticNames
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm
-- Original HOL or_exception=T
example (c : AsmConfigExact 8) : arithName (.binop .or 1 2 (.reg 2)) {c with isa := .x86_64, regCount := 8, avoidRegs := [], twoRegArith := true, validImm := fun _ _ => true} := by
  simp [arithName, regName, regImmName]
-- Original HOL or_wrong=F
example (c : AsmConfigExact 8) : ¬ arithName (.binop .or 1 2 (.reg 3)) {c with isa := .x86_64, regCount := 8, avoidRegs := [], twoRegArith := true, validImm := fun _ _ => true} := by
  simp [arithName, regName, regImmName]
-- Original HOL binop_two=F
example (c : AsmConfigExact 8) : ¬ arithName (.binop .add 1 2 (.reg 2)) {c with isa := .x86_64, regCount := 8, avoidRegs := [], twoRegArith := true, validImm := fun _ _ => true} := by
  simp [arithName, regName, regImmName]
-- Original HOL binop_same=T
example (c : AsmConfigExact 8) : arithName (.binop .add 1 1 (.reg 2)) {c with isa := .x86_64, regCount := 8, avoidRegs := [], twoRegArith := true, validImm := fun _ _ => true} := by
  simp [arithName, regName, regImmName]
-- Original HOL imm_valid=T
example (c : AsmConfigExact 8) : arithName (.binop .add 1 1 (.imm 7)) {c with isa := .riscv, regCount := 8, avoidRegs := [], twoRegArith := false, validImm := fun _ _ => true} := by
  simp [arithName, regName, regImmName]
-- Original HOL shift_zero_lsl=T
example (c : AsmConfigExact 8) : arithName (.shift .lsl 1 1 (.imm 0)) {c with isa := .x86_64, regCount := 8, avoidRegs := [], twoRegArith := true, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL shift_zero_lsr=F
example (c : AsmConfigExact 8) : ¬ arithName (.shift .lsr 1 1 (.imm 0)) {c with isa := .x86_64, regCount := 8, avoidRegs := [], twoRegArith := true, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL shift_width=F
example (c : AsmConfigExact 8) : ¬ arithName (.shift .lsl 1 1 (.imm 8)) {c with isa := .riscv, regCount := 8, avoidRegs := [], twoRegArith := false, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL shift_x86_4=T
example (c : AsmConfigExact 8) : arithName (.shift .lsl 1 1 (.reg 4)) {c with isa := .x86_64, regCount := 8, avoidRegs := [], twoRegArith := true, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL shift_x86_1=F
example (c : AsmConfigExact 8) : ¬ arithName (.shift .lsl 1 1 (.reg 1)) {c with isa := .x86_64, regCount := 8, avoidRegs := [], twoRegArith := true, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL div_riscv=T
example (c : AsmConfigExact 8) : arithName (.div 1 2 3) {c with isa := .riscv, regCount := 8, avoidRegs := [], twoRegArith := false, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL div_x86=F
example (c : AsmConfigExact 8) : ¬ arithName (.div 1 2 3) {c with isa := .x86_64, regCount := 8, avoidRegs := [], twoRegArith := false, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL mul_x86_3=T
example (c : AsmConfigExact 8) : arithName (.longMul 3 0 0 4) {c with isa := .x86_64, regCount := 8, avoidRegs := [], twoRegArith := false, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL mul_x86_2=F
example (c : AsmConfigExact 8) : ¬ arithName (.longMul 2 0 0 4) {c with isa := .x86_64, regCount := 8, avoidRegs := [], twoRegArith := false, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL mul_arm_alias=F
example (c : AsmConfigExact 8) : ¬ arithName (.longMul 1 1 2 3) {c with isa := .armv7, regCount := 8, avoidRegs := [], twoRegArith := false, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL mul_riscv_alias=F
example (c : AsmConfigExact 8) : ¬ arithName (.longMul 1 2 1 3) {c with isa := .riscv, regCount := 8, avoidRegs := [], twoRegArith := false, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL longdiv_3=T
example (c : AsmConfigExact 8) : arithName (.longDiv 0 3 3 0 4) {c with isa := .x86_64, regCount := 8, avoidRegs := [], twoRegArith := false, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL longdiv_2=F
example (c : AsmConfigExact 8) : ¬ arithName (.longDiv 0 2 2 0 4) {c with isa := .x86_64, regCount := 8, avoidRegs := [], twoRegArith := false, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL carry_good=T
example (c : AsmConfigExact 8) : arithName (.addCarry 1 2 3 4) {c with isa := .riscv, regCount := 8, avoidRegs := [], twoRegArith := false, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL carry_alias=F
example (c : AsmConfigExact 8) : ¬ arithName (.addCarry 1 2 3 1) {c with isa := .riscv, regCount := 8, avoidRegs := [], twoRegArith := false, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL addoverflow_right_alias=T
example (c : AsmConfigExact 8) : arithName (.addOverflow 1 2 3 1) {c with isa := .riscv, regCount := 8, avoidRegs := [], twoRegArith := false, validImm := fun _ _ => true} := by
  simp [arithName, regName]
-- Original HOL suboverflow_left_alias=F
example (c : AsmConfigExact 8) : ¬ arithName (.subOverflow 1 2 1 3) {c with isa := .riscv, regCount := 8, avoidRegs := [], twoRegArith := false, validImm := fun _ _ => true} := by
  simp [arithName, regName]
end Flapjack.Test.StackPropsArithmeticNames
