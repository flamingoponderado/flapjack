import Flapjack.Compiler.Backend.StackProps.AddressNames
namespace Flapjack.Test.StackPropsAddressNames
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm
-- Original HOL word_min=T
example (c : AsmConfigExact 8) : addrName .load (.addr 1 254) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], addrOffset := (254,2), hwOffset := (255,1), byteOffset := (0,0)} := by
  simp [addrName, regName, asmAddrOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL word_max=T
example (c : AsmConfigExact 8) : addrName .store (.addr 1 2) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], addrOffset := (254,2), hwOffset := (255,1), byteOffset := (0,0)} := by
  simp [addrName, regName, asmAddrOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL word_low=F
example (c : AsmConfigExact 8) : ¬ addrName .load32 (.addr 1 253) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], addrOffset := (254,2), hwOffset := (255,1), byteOffset := (0,0)} := by
  simp [addrName, regName, asmAddrOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL word_high=F
example (c : AsmConfigExact 8) : ¬ addrName .store32 (.addr 1 3) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], addrOffset := (254,2), hwOffset := (255,1), byteOffset := (0,0)} := by
  simp [addrName, regName, asmAddrOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL half_min=T
example (c : AsmConfigExact 8) : addrName .load16 (.addr 1 255) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], addrOffset := (254,2), hwOffset := (255,1), byteOffset := (0,0)} := by
  simp [addrName, regName, asmHwOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL half_max=T
example (c : AsmConfigExact 8) : addrName .store16 (.addr 1 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], addrOffset := (254,2), hwOffset := (255,1), byteOffset := (0,0)} := by
  simp [addrName, regName, asmHwOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL half_high=F
example (c : AsmConfigExact 8) : ¬ addrName .load16 (.addr 1 2) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], addrOffset := (254,2), hwOffset := (255,1), byteOffset := (0,0)} := by
  simp [addrName, regName, asmHwOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL half_ag32=F
example (c : AsmConfigExact 8) : ¬ addrName .store16 (.addr 1 0) {c with isa := .ag32, regCount := 8, avoidRegs := [0,1], addrOffset := (254,2), hwOffset := (255,1), byteOffset := (0,0)} := by
  simp [addrName, regName, asmHwOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL byte_zero=T
example (c : AsmConfigExact 8) : addrName .load8 (.addr 1 0) {c with isa := .ag32, regCount := 8, avoidRegs := [0,1], addrOffset := (254,2), hwOffset := (255,1), byteOffset := (0,0)} := by
  simp [addrName, regName, asmByteOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL byte_high=F
example (c : AsmConfigExact 8) : ¬ addrName .store8 (.addr 1 1) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], addrOffset := (254,2), hwOffset := (255,1), byteOffset := (0,0)} := by
  simp [addrName, regName, asmByteOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL reg_last=T
example (c : AsmConfigExact 8) : addrName .load (.addr 5 0) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], addrOffset := (254,2), hwOffset := (255,1), byteOffset := (0,0)} := by
  simp [addrName, regName, asmAddrOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL reg_bound=F
example (c : AsmConfigExact 8) : ¬ addrName .load (.addr 6 0) {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], addrOffset := (254,2), hwOffset := (255,1), byteOffset := (0,0)} := by
  simp [addrName, regName, asmAddrOffsetOkExact, asmOffsetOkExact, asmAligned]
end Flapjack.Test.StackPropsAddressNames
