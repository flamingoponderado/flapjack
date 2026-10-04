import Flapjack.Compiler.Backend.LabSem.Inst

/-! Kernel replay of all five original asm_inst dispatch branches.
Inputs and assertions match labsem_inst_probe.out, including failure writes,
Loc memory/registers, unsupported ordinary16 and raw FP payloads. The full
unconditional source frame theorem is checked separately in Inst.lean. -/
set_option maxRecDepth 8192

namespace Flapjack.Test.LabSemInstParity
open Flapjack Flapjack.Compiler.Backend.LabSem

-- lab_inst_skip
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let start := { s with
      regs := (fun _ => .word 99)
      memory := (fun _ => .loc 4 5)
      fpRegs := (fun _ => 9223372036854775808)
      memDomain := fun _ => true
      be := false
      failed := false }
    let t := asmInst (.skip) start
    t = start := by
  simp +decide [asmInst]
    <;> decide +kernel

-- lab_inst_const
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let start := { s with
      regs := (fun _ => .word 99)
      memory := (fun _ => .loc 4 5)
      fpRegs := (fun _ => 9223372036854775808)
      memDomain := fun _ => true
      be := false
      failed := false }
    let t := asmInst (.const 3 27) start
    t.regs 3 = .word 27 ∧ t.regs 1 = .word 99 ∧ t.failed = false := by
  simp +decide [asmInst, updReg]
    <;> decide +kernel

-- lab_inst_arith_or_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let start := { s with
      regs := (fun r => if r=2 then .loc 4 5 else .word 99)
      memory := (fun _ => .loc 4 5)
      fpRegs := (fun _ => 9223372036854775808)
      memDomain := fun _ => true
      be := false
      failed := false }
    let t := asmInst (.arith (.binop .or 0 2 (.reg 2))) start
    t.regs 0 = .loc 4 5 ∧ t.failed = false := by
  simp +decide [asmInst, arithUpd, regImm, updReg]
    <;> decide +kernel

-- lab_inst_arith_or_loc_other
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let start := { s with
      regs := (fun r => if r=2 then .loc 4 5 else if r=3 then .loc 4 5 else .word 99)
      memory := (fun _ => .loc 4 5)
      fpRegs := (fun _ => 9223372036854775808)
      memDomain := fun _ => true
      be := false
      failed := false }
    let t := asmInst (.arith (.binop .or 0 2 (.reg 3))) start
    t.regs 0 = .word 99 ∧ t.failed = true := by
  simp +decide [asmInst, arithUpd, regImm, assertState]
    <;> decide +kernel

-- lab_inst_arith_div_zero
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let start := { s with
      regs := (fun r => if r=3 then .word 0 else .word 99)
      memory := (fun _ => .loc 4 5)
      fpRegs := (fun _ => 9223372036854775808)
      memDomain := fun _ => true
      be := false
      failed := false }
    let t := asmInst (.arith (.div 0 2 3)) start
    t.regs 0 = .word 0 ∧ t.failed = true := by
  simp +decide [asmInst, arithUpd, updReg, assertState]
    <;> decide +kernel

-- lab_inst_arith_shift_invalid
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let start := { s with
      regs := (fun _ => .word 99)
      memory := (fun _ => .loc 4 5)
      fpRegs := (fun _ => 9223372036854775808)
      memDomain := fun _ => true
      be := false
      failed := false }
    let t := asmInst (.arith (.shift .lsl 0 2 (.imm 64))) start
    t.regs 0 = .word 0 ∧ t.failed = true := by
  simp +decide [asmInst, arithUpd, regImm, updReg, assertState, Flapjack.Compiler.Encoders.AsmSem.wordShift]
    <;> decide +kernel

-- lab_inst_mem_load_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let start := { s with
      regs := (fun r => if r=2 then .word 0 else .word 99)
      memory := (fun _ => .loc 4 5)
      fpRegs := (fun _ => 9223372036854775808)
      memDomain := fun _ => true
      be := false
      failed := false }
    let t := asmInst (.mem .load 0 (.addr 2 0)) start
    t.regs 0 = .loc 4 5 ∧ t.failed = false := by
  simp +decide [asmInst, memOp, memLoad, addrValue, updReg, assertState]
    <;> decide +kernel

-- lab_inst_mem_store_unaligned
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let start := { s with
      regs := (fun r => if r=2 then .word 0 else if r=0 then .loc 7 8 else .word 99)
      memory := (fun _ => .loc 4 5)
      fpRegs := (fun _ => 9223372036854775808)
      memDomain := fun _ => true
      be := false
      failed := false }
    let t := asmInst (.mem .store 0 (.addr 2 1)) start
    t.memory 1 = .loc 7 8 ∧ t.failed = true := by
  simp +decide [asmInst, memOp, memStore, addrValue, updMem, assertState]
    <;> decide +kernel

-- lab_inst_mem_load32_loc_failure
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let start := { s with
      regs := (fun r => if r=2 then .word 0 else .word 99)
      memory := (fun _ => .loc 4 5)
      fpRegs := (fun _ => 9223372036854775808)
      memDomain := fun _ => true
      be := false
      failed := false }
    let t := asmInst (.mem .load32 0 (.addr 2 0)) start
    t.regs 0 = .word 99 ∧ t.failed = true := by
  simp +decide [asmInst, memOp, memLoad32, addrValue, assertState, memLoad32Exact]
    <;> decide +kernel

-- lab_inst_mem_load16_unsupported
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let start := { s with
      regs := (fun _ => .word 99)
      memory := (fun _ => .loc 4 5)
      fpRegs := (fun _ => 9223372036854775808)
      memDomain := fun _ => true
      be := false
      failed := false }
    let t := asmInst (.mem .load16 0 (.addr 2 0)) start
    t.regs 0 = .word 99 ∧ t.memory 0 = .loc 4 5 ∧ t.failed = true := by
  simp +decide [asmInst, memOp, assertState]
    <;> decide +kernel

-- lab_inst_mem_store16_unsupported
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let start := { s with
      regs := (fun _ => .word 99)
      memory := (fun _ => .loc 4 5)
      fpRegs := (fun _ => 9223372036854775808)
      memDomain := fun _ => true
      be := false
      failed := false }
    let t := asmInst (.mem .store16 0 (.addr 2 0)) start
    t.regs 0 = .word 99 ∧ t.memory 0 = .loc 4 5 ∧ t.failed = true := by
  simp +decide [asmInst, memOp, assertState]
    <;> decide +kernel

-- lab_inst_fp_mov_payload
end Flapjack.Test.LabSemInstParity
