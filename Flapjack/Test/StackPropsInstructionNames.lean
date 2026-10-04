import Flapjack.Compiler.Backend.StackProps.InstructionNames

namespace Flapjack.Test.StackPropsInstructionNames
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm

-- Original HOL skip=T
example (c : AsmConfigExact 8) : instName {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true, addrOffset := (0,0)} (.skip) := by
  dsimp [instName, regName, addrName, arithName, regImmName,
    asmAddrOffsetOkExact, asmOffsetOkExact, asmAligned] <;> simp

-- Original HOL const_last=T
example (c : AsmConfigExact 8) : instName {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true, addrOffset := (0,0)} (.const 5 255) := by
  dsimp [instName, regName, addrName, arithName, regImmName,
    asmAddrOffsetOkExact, asmOffsetOkExact, asmAligned] <;> simp

-- Original HOL const_bound=F
example (c : AsmConfigExact 8) : ¬ instName {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true, addrOffset := (0,0)} (.const 6 0) := by
  dsimp [instName, regName, addrName, arithName, regImmName,
    asmAddrOffsetOkExact, asmOffsetOkExact, asmAligned] <;> simp

-- Original HOL mem_good=T
example (c : AsmConfigExact 8) : instName {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true, addrOffset := (0,0)} (.mem .load 5 (.addr 1 0)) := by
  dsimp [instName, regName, addrName, arithName, regImmName,
    asmAddrOffsetOkExact, asmOffsetOkExact, asmAligned] <;> simp

-- Original HOL mem_destination=F
example (c : AsmConfigExact 8) : ¬ instName {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true, addrOffset := (0,0)} (.mem .load 6 (.addr 1 0)) := by
  dsimp [instName, regName, addrName, arithName, regImmName,
    asmAddrOffsetOkExact, asmOffsetOkExact, asmAligned] <;> simp

-- Original HOL mem_base=F
example (c : AsmConfigExact 8) : ¬ instName {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true, addrOffset := (0,0)} (.mem .load 1 (.addr 6 0)) := by
  dsimp [instName, regName, addrName, arithName, regImmName,
    asmAddrOffsetOkExact, asmOffsetOkExact, asmAligned] <;> simp

-- Original HOL arith_good=T
example (c : AsmConfigExact 8) : instName {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true, addrOffset := (0,0)} (.arith (.binop .add 1 1 (.reg 2))) := by
  dsimp [instName, regName, addrName, arithName, regImmName,
    asmAddrOffsetOkExact, asmOffsetOkExact, asmAligned] <;> simp

-- Original HOL arith_bad=F
example (c : AsmConfigExact 8) : ¬ instName {c with isa := .riscv, regCount := 8, avoidRegs := [0,1], fpRegCount := 4, twoRegArith := true, addrOffset := (0,0)} (.arith (.binop .add 1 2 (.reg 2))) := by
  dsimp [instName, regName, addrName, arithName, regImmName,
    asmAddrOffsetOkExact, asmOffsetOkExact, asmAligned] <;> simp

-- Original HOL fp_good=T
end Flapjack.Test.StackPropsInstructionNames
