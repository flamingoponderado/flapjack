import Flapjack.Compiler.Backend.StackProps.FloatNames
namespace Flapjack.Test.StackPropsFloatNames
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm
-- Original HOL fpLess=T
example (c : AsmConfigExact 64) : fpName (.fpLess 1 0 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, regName, asmFpRegOkExact]
-- Original HOL fpLessEqual=T
example (c : AsmConfigExact 64) : fpName (.fpLessEqual 1 0 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, regName, asmFpRegOkExact]
-- Original HOL fpEqual=T
example (c : AsmConfigExact 64) : fpName (.fpEqual 1 0 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, regName, asmFpRegOkExact]
-- Original HOL fpAbs=T
example (c : AsmConfigExact 64) : fpName (.fpAbs 0 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fpAbs_alias=F
example (c : AsmConfigExact 64) : ¬ fpName (.fpAbs 0 0) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fpNeg=T
example (c : AsmConfigExact 64) : fpName (.fpNeg 0 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fpNeg_alias=F
example (c : AsmConfigExact 64) : ¬ fpName (.fpNeg 0 0) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fpSqrt=T
example (c : AsmConfigExact 64) : fpName (.fpSqrt 0 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fpMov=T
example (c : AsmConfigExact 64) : fpName (.fpMov 0 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fpToInt=T
example (c : AsmConfigExact 64) : fpName (.fpToInt 0 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fpFromInt=T
example (c : AsmConfigExact 64) : fpName (.fpFromInt 0 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fpAdd=T
example (c : AsmConfigExact 64) : fpName (.fpAdd 0 0 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fpSub=T
example (c : AsmConfigExact 64) : fpName (.fpSub 0 0 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fpMul=T
example (c : AsmConfigExact 64) : fpName (.fpMul 0 0 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fpDiv=T
example (c : AsmConfigExact 64) : fpName (.fpDiv 0 0 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL binary_mismatch=F
example (c : AsmConfigExact 64) : ¬ fpName (.fpAdd 0 1 2) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL binary_three_reg=T
example (c : AsmConfigExact 64) : fpName (.fpAdd 0 1 2) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := false} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fma_arm=T
example (c : AsmConfigExact 64) : fpName (.fpFma 0 1 2) {c with isa := .armv7, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fma_riscv=F
example (c : AsmConfigExact 64) : ¬ fpName (.fpFma 0 1 2) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fma_count2=F
example (c : AsmConfigExact 64) : ¬ fpName (.fpFma 0 1 1) {c with isa := .armv7, regCount := 8, avoidRegs := [0,1], fpRegCount := 2, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL fpMovToReg_32=T
example (c : AsmConfigExact 32) : fpName (.fpMovToReg 1 2 0) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, regName, asmFpRegOkExact]
-- Original HOL fpMovFromReg_32=T
example (c : AsmConfigExact 32) : fpName (.fpMovFromReg 0 1 2) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, regName, asmFpRegOkExact]
-- Original HOL move32_alias=F
example (c : AsmConfigExact 32) : ¬ fpName (.fpMovToReg 1 1 0) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, regName, asmFpRegOkExact]
-- Original HOL move32_bound=F
example (c : AsmConfigExact 32) : ¬ fpName (.fpMovFromReg 0 1 6) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, regName, asmFpRegOkExact]
-- Original HOL move64_ignored=T
example (c : AsmConfigExact 64) : fpName (.fpMovToReg 1 99 0) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, regName, asmFpRegOkExact]
-- Original HOL fp_bound=F
example (c : AsmConfigExact 64) : ¬ fpName (.fpSqrt 0 4) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, asmFpRegOkExact]
-- Original HOL logical_bound=F
example (c : AsmConfigExact 64) : ¬ fpName (.fpLess 6 0 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true} := by
  simp [fpName, regName, asmFpRegOkExact]
end Flapjack.Test.StackPropsFloatNames
