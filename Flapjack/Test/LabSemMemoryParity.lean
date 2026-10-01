import Flapjack.Compiler.Backend.LabSem.Memory

/-! Native direct kernel replays of labsem_memory_probe.out. All8 mem_op cases,
raw failing writes, narrow alignment/domain/type errors, endian/resizing,
sticky failure, address wrapping and positive dimensions smaller than one byte. -/
set_option maxRecDepth 4096

namespace Flapjack.Test.LabSemMemoryParity
open Flapjack.Compiler.Backend.LabSem

-- lab_mem_load_word
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 1234605616436508552 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = false := by
  simp [memOp, memLoad, addrValue, assertState, updReg] <;> decide +kernel

-- lab_mem_load_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .loc 4 5 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .loc 4 5 ∧ t.memory 0 = .loc 4 5 ∧ t.failed = false := by
  simp [memOp, memLoad, addrValue, assertState, updReg] <;> decide +kernel

-- lab_mem_store_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .loc 4 5 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .loc 4 5 ∧ t.memory 0 = .loc 4 5 ∧ t.failed = false := by
  simp [memOp, memStore, addrValue, assertState, updMem] <;> decide +kernel

-- lab_mem_load_unaligned_write
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load 0 (.addr 2 1) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 77 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memLoad, addrValue, assertState, updReg] <;> decide +kernel

-- lab_mem_store_unaligned_write
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store 0 (.addr 2 1) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .loc 4 5 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .loc 4 5 ∧ t.memory 1 = .loc 4 5 ∧ t.failed = true := by
  simp [memOp, memStore, addrValue, assertState, updMem] <;> decide +kernel

-- lab_mem_load_domain_write
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 8 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun a => decide (a = 0), be := false, failed := false }
    t.regs 0 = .word 77 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memLoad, addrValue, assertState, updReg] <;> decide +kernel

-- lab_mem_store_domain_write
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 8 else if r = 0 then .loc 4 5 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun a => decide (a = 0), be := false, failed := false }
    t.regs 0 = .loc 4 5 ∧ t.memory 8 = .loc 4 5 ∧ t.failed = true := by
  simp [memOp, memStore, addrValue, assertState, updMem] <;> decide +kernel

-- lab_mem_load_address_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .loc 4 5 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 99 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memLoad, addrValue, assertState] <;> decide +kernel

-- lab_mem_store_address_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .loc 4 5 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 99 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memStore, addrValue, assertState] <;> decide +kernel

-- lab_mem_address_wrap
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load 0 (.addr 2 1) { s with regs := fun r => if r = 2 then .word 18446744073709551615 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 1234605616436508552 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = false := by
  simp [memOp, memLoad, addrValue, assertState, updReg] <;> decide +kernel

-- lab_mem_load32_le_low
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load32 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun a => decide (a = 0), be := false, failed := false }
    t.regs 0 = .word 1432778632 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = false := by
  simp [memOp, memLoad32, addrValue, updReg, Flapjack.memLoad32Exact, Flapjack.riscvAlignedHOL, Flapjack.riscvByteAlignHOL, Flapjack.wordOfBytesHOL8, Flapjack.getByteHOL8, Flapjack.setByteHOL8, Flapjack.byteIndexHOL] <;> decide +kernel

-- lab_mem_load32_le_high
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load32 0 (.addr 2 4) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun a => decide (a = 0), be := false, failed := false }
    t.regs 0 = .word 287454020 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = false := by
  simp [memOp, memLoad32, addrValue, updReg, Flapjack.memLoad32Exact, Flapjack.riscvAlignedHOL, Flapjack.riscvByteAlignHOL, Flapjack.wordOfBytesHOL8, Flapjack.getByteHOL8, Flapjack.setByteHOL8, Flapjack.byteIndexHOL] <;> decide +kernel

-- lab_mem_load32_be_high
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load32 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun a => decide (a = 0), be := true, failed := false }
    t.regs 0 = .word 287454020 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = false := by
  simp [memOp, memLoad32, addrValue, updReg, Flapjack.memLoad32Exact, Flapjack.riscvAlignedHOL, Flapjack.riscvByteAlignHOL, Flapjack.wordOfBytesHOL8, Flapjack.getByteHOL8, Flapjack.setByteHOL8, Flapjack.byteIndexHOL] <;> decide +kernel

-- lab_mem_load32_be_low
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load32 0 (.addr 2 4) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun a => decide (a = 0), be := true, failed := false }
    t.regs 0 = .word 1432778632 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = false := by
  simp [memOp, memLoad32, addrValue, updReg, Flapjack.memLoad32Exact, Flapjack.riscvAlignedHOL, Flapjack.riscvByteAlignHOL, Flapjack.wordOfBytesHOL8, Flapjack.getByteHOL8, Flapjack.setByteHOL8, Flapjack.byteIndexHOL] <;> decide +kernel

-- lab_mem_load32_unsigned
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load32 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 4294967295 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 4294967295 ∧ t.memory 0 = .word 4294967295 ∧ t.failed = false := by
  simp [memOp, memLoad32, addrValue, updReg, Flapjack.memLoad32Exact, Flapjack.riscvAlignedHOL, Flapjack.riscvByteAlignHOL, Flapjack.wordOfBytesHOL8, Flapjack.getByteHOL8, Flapjack.setByteHOL8, Flapjack.byteIndexHOL] <;> decide +kernel

-- lab_mem_load32_unaligned
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load32 0 (.addr 2 1) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 99 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memLoad32, addrValue, assertState, Flapjack.memLoad32Exact, Flapjack.riscvAlignedHOL] <;> decide +kernel

-- lab_mem_load32_domain
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load32 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => false, be := false, failed := false }
    t.regs 0 = .word 99 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memLoad32, addrValue, assertState, Flapjack.memLoad32Exact, Flapjack.riscvAlignedHOL, Flapjack.riscvByteAlignHOL] <;> decide +kernel

-- lab_mem_load32_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load32 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .loc 4 5 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 99 ∧ t.memory 0 = .loc 4 5 ∧ t.failed = true := by
  simp [memOp, memLoad32, addrValue, assertState, Flapjack.memLoad32Exact, Flapjack.riscvAlignedHOL, Flapjack.riscvByteAlignHOL] <;> decide +kernel

-- lab_mem_load32_address_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load32 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .loc 4 5 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 99 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memLoad32, addrValue, assertState] <;> decide +kernel

-- lab_mem_store32_le_narrow
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store32 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 659994430685 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 659994430685 ∧ t.memory 0 = .word 1234605617868164317 ∧ t.failed = false := by
  simp [memOp, memStore32, addrValue, Flapjack.memStore32Exact, Flapjack.riscvAlignedHOL, Flapjack.riscvByteAlignHOL, Flapjack.getByteHOL8, Flapjack.setByteHOL8, Flapjack.byteIndexHOL] <;> decide +kernel

-- lab_mem_store32_be_narrow
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store32 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 659994430685 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := true, failed := false }
    t.regs 0 = .word 659994430685 ∧ t.memory 0 = .word 12302652058085259144 ∧ t.failed = false := by
  simp [memOp, memStore32, addrValue, Flapjack.memStore32Exact, Flapjack.riscvAlignedHOL, Flapjack.riscvByteAlignHOL, Flapjack.getByteHOL8, Flapjack.setByteHOL8, Flapjack.byteIndexHOL] <;> decide +kernel

-- lab_mem_store32_upper_half
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store32 0 (.addr 2 4) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 2864434397 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun a => decide (a = 0), be := false, failed := false }
    t.regs 0 = .word 2864434397 ∧ t.memory 0 = .word 12302652058085259144 ∧ t.failed = false := by
  simp [memOp, memStore32, addrValue, Flapjack.memStore32Exact, Flapjack.riscvAlignedHOL, Flapjack.riscvByteAlignHOL, Flapjack.getByteHOL8, Flapjack.setByteHOL8, Flapjack.byteIndexHOL] <;> decide +kernel

-- lab_mem_store32_unaligned
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store32 0 (.addr 2 1) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 2864434397 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 2864434397 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memStore32, addrValue, assertState, Flapjack.memStore32Exact, Flapjack.riscvAlignedHOL] <;> decide +kernel

-- lab_mem_store32_domain
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store32 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 2864434397 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => false, be := false, failed := false }
    t.regs 0 = .word 2864434397 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memStore32, addrValue, assertState, Flapjack.memStore32Exact, Flapjack.riscvAlignedHOL, Flapjack.riscvByteAlignHOL] <;> decide +kernel

-- lab_mem_store32_source_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store32 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .loc 4 5 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .loc 4 5 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memStore32, addrValue, assertState] <;> decide +kernel

-- lab_mem_store32_memory_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store32 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 2864434397 else .word 99, memory := fun a => if a = 0 then .loc 4 5 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 2864434397 ∧ t.memory 0 = .loc 4 5 ∧ t.failed = true := by
  simp [memOp, memStore32, addrValue, assertState, Flapjack.memStore32Exact, Flapjack.riscvAlignedHOL, Flapjack.riscvByteAlignHOL] <;> decide +kernel

-- lab_mem_load8_le
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load8 0 (.addr 2 1) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun a => decide (a = 0), be := false, failed := false }
    t.regs 0 = .word 119 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = false := by
  simp [memOp, memLoadByte, addrValue, updReg, Flapjack.memLoadByteAuxExact, Flapjack.riscvByteAlignHOL, Flapjack.getByteHOL8, Flapjack.byteIndexHOL] <;> decide +kernel

-- lab_mem_load8_be
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load8 0 (.addr 2 1) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun a => decide (a = 0), be := true, failed := false }
    t.regs 0 = .word 34 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = false := by
  simp [memOp, memLoadByte, addrValue, updReg, Flapjack.memLoadByteAuxExact, Flapjack.riscvByteAlignHOL, Flapjack.getByteHOL8, Flapjack.byteIndexHOL] <;> decide +kernel

-- lab_mem_load8_unsigned
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load8 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 255 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 255 ∧ t.memory 0 = .word 255 ∧ t.failed = false := by
  simp [memOp, memLoadByte, addrValue, updReg, Flapjack.memLoadByteAuxExact, Flapjack.riscvByteAlignHOL, Flapjack.getByteHOL8, Flapjack.byteIndexHOL] <;> decide +kernel

-- lab_mem_load8_domain_base
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load8 0 (.addr 2 1) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun a => decide (a = 1), be := false, failed := false }
    t.regs 0 = .word 99 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memLoadByte, addrValue, assertState, Flapjack.memLoadByteAuxExact, Flapjack.riscvByteAlignHOL] <;> decide +kernel

-- lab_mem_load8_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load8 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .loc 4 5 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 99 ∧ t.memory 0 = .loc 4 5 ∧ t.failed = true := by
  simp [memOp, memLoadByte, addrValue, assertState, Flapjack.memLoadByteAuxExact, Flapjack.riscvByteAlignHOL] <;> decide +kernel

-- lab_mem_load8_address_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load8 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .loc 4 5 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 99 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memLoadByte, addrValue, assertState] <;> decide +kernel

-- lab_mem_store8_le_narrow
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store8 0 (.addr 2 1) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 4660 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun a => decide (a = 0), be := false, failed := false }
    t.regs 0 = .word 4660 ∧ t.memory 0 = .word 1234605616436491400 ∧ t.failed = false := by
  simp [memOp, memStoreByte, addrValue, Flapjack.memStoreByteAuxExact, Flapjack.riscvByteAlignHOL, Flapjack.setByteHOL8, Flapjack.byteIndexHOL] <;> decide +kernel

-- lab_mem_store8_be_narrow
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store8 0 (.addr 2 1) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 4660 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun a => decide (a = 0), be := true, failed := false }
    t.regs 0 = .word 4660 ∧ t.memory 0 = .word 1239672166017300360 ∧ t.failed = false := by
  simp [memOp, memStoreByte, addrValue, Flapjack.memStoreByteAuxExact, Flapjack.riscvByteAlignHOL, Flapjack.setByteHOL8, Flapjack.byteIndexHOL] <;> decide +kernel

-- lab_mem_store8_domain_base
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store8 0 (.addr 2 1) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 4660 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun a => decide (a = 1), be := false, failed := false }
    t.regs 0 = .word 4660 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memStoreByte, addrValue, assertState, Flapjack.memStoreByteAuxExact, Flapjack.riscvByteAlignHOL] <;> decide +kernel

-- lab_mem_store8_source_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store8 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .loc 4 5 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .loc 4 5 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memStoreByte, addrValue, assertState] <;> decide +kernel

-- lab_mem_store8_memory_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store8 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 4660 else .word 99, memory := fun a => if a = 0 then .loc 4 5 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 4660 ∧ t.memory 0 = .loc 4 5 ∧ t.failed = true := by
  simp [memOp, memStoreByte, addrValue, assertState, Flapjack.memStoreByteAuxExact, Flapjack.riscvByteAlignHOL] <;> decide +kernel

-- lab_mem_load16_unsupported
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load16 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 99 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, assertState] <;> decide +kernel

-- lab_mem_load16_loc_address
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load16 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .loc 4 5 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 99 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, assertState] <;> decide +kernel

-- lab_mem_store16_unsupported
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store16 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 99 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, assertState] <;> decide +kernel

-- lab_mem_store16_loc_address
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store16 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .loc 4 5 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 99 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, assertState] <;> decide +kernel

-- lab_mem_sticky_load
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .load 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := true }
    t.regs 0 = .word 1234605616436508552 ∧ t.memory 0 = .word 1234605616436508552 ∧ t.failed = true := by
  simp [memOp, memLoad, addrValue, assertState, updReg] <;> decide +kernel

-- lab_mem_sticky_store
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Unit) :
    let t := memOp .store 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .loc 4 5 else .word 99, memory := fun a => if a = 0 then .word 1234605616436508552 else .word 77, memDomain := fun _ => true, be := false, failed := true }
    t.regs 0 = .loc 4 5 ∧ t.memory 0 = .loc 4 5 ∧ t.failed = true := by
  simp [memOp, memStore, addrValue, assertState, updMem] <;> decide +kernel

-- lab_mem_width1_address0
example (s : Flapjack.Compiler.Backend.LabSem.State 1 Unit Unit) :
    let t := memOp .load 0 (.addr 2 0) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .loc 4 5 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .loc 4 5 ∧ t.memory 0 = .loc 4 5 ∧ t.failed = false := by
  simp [memOp, memLoad, addrValue, assertState, updReg] <;> decide +kernel

-- lab_mem_width1_address1
example (s : Flapjack.Compiler.Backend.LabSem.State 1 Unit Unit) :
    let t := memOp .load 0 (.addr 2 1) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .loc 4 5 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 77 ∧ t.memory 0 = .loc 4 5 ∧ t.failed = true := by
  simp [memOp, memLoad, addrValue, assertState, updReg] <;> decide +kernel

-- lab_mem_width8_address1
example (s : Flapjack.Compiler.Backend.LabSem.State 8 Unit Unit) :
    let t := memOp .load 0 (.addr 2 1) { s with regs := fun r => if r = 2 then .word 0 else if r = 0 then .word 99 else .word 99, memory := fun a => if a = 0 then .loc 4 5 else .word 77, memDomain := fun _ => true, be := false, failed := false }
    t.regs 0 = .word 77 ∧ t.memory 0 = .loc 4 5 ∧ t.failed = false := by
  simp [memOp, memLoad, addrValue, assertState, updReg] <;> decide +kernel

end Flapjack.Test.LabSemMemoryParity
