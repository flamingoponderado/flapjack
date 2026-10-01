import Flapjack.Compiler.Backend.LabSem.SharedMemory

/-! Kernel replay of the original labsem_shared_memory_probe.out rows.
Checks actual protocol bytes/configuration, all eight operations, final and
returning FFI states, size/domain/alias/clock and narrow-width boundaries. -/
set_option maxRecDepth 8192

namespace Flapjack.Test.LabSemSharedMemoryParity
open Flapjack Flapjack.Compiler.Backend.LabSem

-- lab_shared_load
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [0] ∧ input = [8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102, 85, 68, 51, 34, 17] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedRead, configuration := [0], bytes := [8, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 102, 85, 68, 51, 34, 17] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, wordOfBytesHOL8, setByteHOL8, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_load8
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [1] ∧ input = [8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load8 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102, 85, 68, 51, 34, 17] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedRead, configuration := [1], bytes := [8, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 102, 85, 68, 51, 34, 17] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, wordOfBytesHOL8, setByteHOL8, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_load16
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [2] ∧ input = [8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load16 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102, 85, 68, 51, 34, 17] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedRead, configuration := [2], bytes := [8, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 102, 85, 68, 51, 34, 17] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, wordOfBytesHOL8, setByteHOL8, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_load32
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [4] ∧ input = [8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load32 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102, 85, 68, 51, 34, 17] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedRead, configuration := [4], bytes := [8, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 102, 85, 68, 51, 34, 17] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, wordOfBytesHOL8, setByteHOL8, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_store
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [0] ∧ input = [136, 119, 102, 85, 68, 51, 34, 17, 8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17, 8, 0, 0, 0, 0, 0, 0, 0] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102, 85, 68, 51, 34, 17, 8, 0, 0, 0, 0, 0, 0, 0] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedWrite, configuration := [0], bytes := [136, 119, 102, 85, 68, 51, 34, 17, 8, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 102, 85, 68, 51, 34, 17, 8, 0, 0, 0, 0, 0, 0, 0] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemStore, sharedMemoryWordBytes, addrValue, incPc, decClock, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_store8
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [1] ∧ input = [136, 8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 8, 0, 0, 0, 0, 0, 0, 0] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store8 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 8, 0, 0, 0, 0, 0, 0, 0] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedWrite, configuration := [1], bytes := [136, 8, 0, 0, 0, 0, 0, 0, 0].zip [136, 8, 0, 0, 0, 0, 0, 0, 0] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemStore, sharedMemoryWordBytes, addrValue, incPc, decClock, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_store16
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [2] ∧ input = [136, 119, 8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 8, 0, 0, 0, 0, 0, 0, 0] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store16 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 8, 0, 0, 0, 0, 0, 0, 0] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedWrite, configuration := [2], bytes := [136, 119, 8, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 8, 0, 0, 0, 0, 0, 0, 0] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemStore, sharedMemoryWordBytes, addrValue, incPc, decClock, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_store32
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [4] ∧ input = [136, 119, 102, 85, 8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 8, 0, 0, 0, 0, 0, 0, 0] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store32 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102, 85, 8, 0, 0, 0, 0, 0, 0, 0] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedWrite, configuration := [4], bytes := [136, 119, 102, 85, 8, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 102, 85, 8, 0, 0, 0, 0, 0, 0, 0] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemStore, sharedMemoryWordBytes, addrValue, incPc, decClock, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_load16_unaligned
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 9 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [2] ∧ input = [9, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load16 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102, 85, 68, 51, 34, 17] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedRead, configuration := [2], bytes := [9, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 102, 85, 68, 51, 34, 17] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, wordOfBytesHOL8, setByteHOL8, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_store16_unaligned
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 9 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [2] ∧ input = [136, 119, 9, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 9, 0, 0, 0, 0, 0, 0, 0] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store16 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 9, 0, 0, 0, 0, 0, 0, 0] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedWrite, configuration := [2], bytes := [136, 119, 9, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 9, 0, 0, 0, 0, 0, 0, 0] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemStore, sharedMemoryWordBytes, addrValue, incPc, decClock, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_load_word_unaligned
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 9 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [0] ∧ input = [9, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load 0 (.addr 2 0) start with
    | none => True
    | some _ => False := by
  simp +decide [shareMemOp, shareMemLoad, addrValue]
    <;> decide +kernel

-- lab_shared_store_word_unaligned
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 9 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [0] ∧ input = [136, 119, 102, 85, 68, 51, 34, 17, 9, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17, 9, 0, 0, 0, 0, 0, 0, 0] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store 0 (.addr 2 0) start with
    | none => True
    | some _ => False := by
  simp +decide [shareMemOp, shareMemStore, addrValue]
    <;> decide +kernel

-- lab_shared_load_word_domain
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 0)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [0] ∧ input = [8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load 0 (.addr 2 0) start with
    | none => True
    | some _ => False := by
  simp +decide [shareMemOp, shareMemLoad, addrValue]
    <;> decide +kernel

-- lab_shared_store_word_domain
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 0)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [0] ∧ input = [136, 119, 102, 85, 68, 51, 34, 17, 8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17, 8, 0, 0, 0, 0, 0, 0, 0] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store 0 (.addr 2 0) start with
    | none => True
    | some _ => False := by
  simp +decide [shareMemOp, shareMemStore, addrValue]
    <;> decide +kernel

-- lab_shared_load_narrow_domain
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 9 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 9)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [1] ∧ input = [9, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load8 0 (.addr 2 0) start with
    | none => True
    | some _ => False := by
  simp +decide [shareMemOp, shareMemLoad, addrValue]
    <;> decide +kernel

-- lab_shared_store_narrow_domain
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 9 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 9)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [1] ∧ input = [136, 9, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 9, 0, 0, 0, 0, 0, 0, 0] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store8 0 (.addr 2 0) start with
    | none => True
    | some _ => False := by
  simp +decide [shareMemOp, shareMemStore, addrValue]
    <;> decide +kernel

-- lab_shared_load_address_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .loc 4 5 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [0] ∧ input = [0, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load 0 (.addr 2 0) start with
    | none => True
    | some _ => False := by
  simp +decide [shareMemOp, shareMemLoad, addrValue]
    <;> decide +kernel

-- lab_shared_store_address_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .loc 4 5 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [1] ∧ input = [136, 0, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 0, 0, 0, 0, 0, 0, 0, 0] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store8 0 (.addr 2 0) start with
    | none => True
    | some _ => False := by
  simp +decide [shareMemOp, shareMemStore, addrValue]
    <;> decide +kernel

-- lab_shared_store_value_loc
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .loc 4 5 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [2] ∧ input = [0, 0, 8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [0, 0, 8, 0, 0, 0, 0, 0, 0, 0] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store16 0 (.addr 2 0) start with
    | none => True
    | some _ => False := by
  simp +decide [shareMemOp, shareMemStore]
    <;> decide +kernel

-- lab_shared_load_final
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [0] ∧ input = [8, 0, 0, 0, 0, 0, 0, 0] then .final .diverged else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load 0 (.addr 2 0) start with
    | some (.final event, t) => event.name = .sharedMem .mappedRead ∧ event.configuration = [0] ∧ event.bytes = [8, 0, 0, 0, 0, 0, 0, 0] ∧ event.outcome = .diverged ∧ t = start
    | _ => False := by
  simp +decide [shareMemOp, shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_store_final
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [4] ∧ input = [136, 119, 102, 85, 8, 0, 0, 0, 0, 0, 0, 0] then .final .diverged else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store32 0 (.addr 2 0) start with
    | some (.final event, t) => event.name = .sharedMem .mappedWrite ∧ event.configuration = [4] ∧ event.bytes = [136, 119, 102, 85, 8, 0, 0, 0, 0, 0, 0, 0] ∧ event.outcome = .diverged ∧ t = start
    | _ => False := by
  simp +decide [shareMemOp, shareMemStore, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_load_wrong_length
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [0] ∧ input = [8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [8, 0, 0, 0, 0, 0, 0, 0, 255] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load 0 (.addr 2 0) start with
    | some (.final event, t) => event.name = .sharedMem .mappedRead ∧ event.configuration = [0] ∧ event.bytes = [8, 0, 0, 0, 0, 0, 0, 0] ∧ event.outcome = .failed ∧ t = start
    | _ => False := by
  simp +decide [shareMemOp, shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_store_wrong_length
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [1] ∧ input = [136, 8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 8, 0, 0, 0, 0, 0, 0, 0, 255] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store8 0 (.addr 2 0) start with
    | some (.final event, t) => event.name = .sharedMem .mappedWrite ∧ event.configuration = [1] ∧ event.bytes = [136, 8, 0, 0, 0, 0, 0, 0, 0] ∧ event.outcome = .failed ∧ t = start
    | _ => False := by
  simp +decide [shareMemOp, shareMemStore, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_load_zero_clock
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [0] ∧ input = [8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17] else .final .diverged) 10
      pc := 3
      clock := 0
      failed := true
      be := false }
    match shareMemOp .load 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102, 85, 68, 51, 34, 17] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedRead, configuration := [0], bytes := [8, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 102, 85, 68, 51, 34, 17] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 0 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, wordOfBytesHOL8, setByteHOL8, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_store_zero_clock
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [2] ∧ input = [136, 119, 8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 8, 0, 0, 0, 0, 0, 0, 0] else .final .diverged) 10
      pc := 3
      clock := 0
      failed := true
      be := false }
    match shareMemOp .store16 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 8, 0, 0, 0, 0, 0, 0, 0] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedWrite, configuration := [2], bytes := [136, 119, 8, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 8, 0, 0, 0, 0, 0, 0, 0] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 0 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemStore, sharedMemoryWordBytes, addrValue, incPc, decClock, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_load_address_alias
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [2] ∧ input = [8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load16 2 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102, 85, 68, 51, 34, 17] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedRead, configuration := [2], bytes := [8, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 102, 85, 68, 51, 34, 17] }] ∧ t.ffi = ffi ∧ t.regs 2 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, wordOfBytesHOL8, setByteHOL8, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_load_protocol_ignores_be
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [2] ∧ input = [8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := true }
    match shareMemOp .load16 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102, 85, 68, 51, 34, 17] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedRead, configuration := [2], bytes := [8, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 102, 85, 68, 51, 34, 17] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, wordOfBytesHOL8, setByteHOL8, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_store_protocol_ignores_be
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 8 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [4] ∧ input = [136, 119, 102, 85, 8, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 8, 0, 0, 0, 0, 0, 0, 0] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := true }
    match shareMemOp .store32 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102, 85, 8, 0, 0, 0, 0, 0, 0, 0] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedWrite, configuration := [4], bytes := [136, 119, 102, 85, 8, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 102, 85, 8, 0, 0, 0, 0, 0, 0, 0] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemStore, sharedMemoryWordBytes, addrValue, incPc, decClock, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_load24_alignment
example (s : Flapjack.Compiler.Backend.LabSem.State 24 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 5 else if r=0 then .word 6715272 else .word 99)
      sharedMemDomain := fun a => decide (a = 4)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [1] ∧ input = [5, 0, 0] then .ret (_host+1) [136, 119, 102] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load8 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedRead, configuration := [1], bytes := [5, 0, 0].zip [136, 119, 102] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 6715272 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, wordOfBytesHOL8, setByteHOL8, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_store24_alignment
example (s : Flapjack.Compiler.Backend.LabSem.State 24 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 5 else if r=0 then .word 6715272 else .word 99)
      sharedMemDomain := fun a => decide (a = 4)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [2] ∧ input = [136, 119, 5, 0, 0] then .ret (_host+1) [136, 119, 5, 0, 0] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store16 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 5, 0, 0] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedWrite, configuration := [2], bytes := [136, 119, 5, 0, 0].zip [136, 119, 5, 0, 0] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 6715272 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemStore, sharedMemoryWordBytes, addrValue, incPc, decClock, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_load1_empty
example (s : Flapjack.Compiler.Backend.LabSem.State 1 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 0 else if r=0 then .word 0 else .word 99)
      sharedMemDomain := fun a => decide (a = 0)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [0] ∧ input = [] then .ret (_host+1) [] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedRead, configuration := [0], bytes := [].zip [] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 0 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, wordOfBytesHOL8, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_store1_empty
example (s : Flapjack.Compiler.Backend.LabSem.State 1 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 0 else if r=0 then .word 0 else .word 99)
      sharedMemDomain := fun a => decide (a = 0)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [2] ∧ input = [] then .ret (_host+1) [] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store16 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedWrite, configuration := [2], bytes := [].zip [] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 0 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemStore, sharedMemoryWordBytes, addrValue, incPc, decClock, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_load1_mod0
example (s : Flapjack.Compiler.Backend.LabSem.State 1 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 1 else if r=0 then .word 0 else .word 99)
      sharedMemDomain := fun a => decide (a = 1)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [0] ∧ input = [] then .ret (_host+1) [] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load 0 (.addr 2 0) start with
    | none => True
    | some _ => False := by
  simp +decide [shareMemOp, shareMemLoad, addrValue]
    <;> decide +kernel

-- lab_shared_store1_mod0
example (s : Flapjack.Compiler.Backend.LabSem.State 1 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 1 else if r=0 then .word 0 else .word 99)
      sharedMemDomain := fun a => decide (a = 1)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [0] ∧ input = [] then .ret (_host+1) [] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store 0 (.addr 2 0) start with
    | none => True
    | some _ => False := by
  simp +decide [shareMemOp, shareMemStore, addrValue]
    <;> decide +kernel

-- lab_shared_load8_word
example (s : Flapjack.Compiler.Backend.LabSem.State 8 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 1 else if r=0 then .word 136 else .word 99)
      sharedMemDomain := fun a => decide (a = 1)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [0] ∧ input = [1] then .ret (_host+1) [136] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedRead, configuration := [0], bytes := [1].zip [136] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 136 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, wordOfBytesHOL8, setByteHOL8, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_store8_short_take16
example (s : Flapjack.Compiler.Backend.LabSem.State 8 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 1 else if r=0 then .word 136 else .word 99)
      sharedMemDomain := fun a => decide (a = 1)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [2] ∧ input = [136, 1] then .ret (_host+1) [136, 1] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .store16 0 (.addr 2 0) start with
    | some (.ret ffi bytes, t) => bytes = [136, 1] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedWrite, configuration := [2], bytes := [136, 1].zip [136, 1] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 136 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemStore, sharedMemoryWordBytes, addrValue, incPc, decClock, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_load_size256
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 9 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [0] ∧ input = [9, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemLoad 0 (.addr 2 0) start 256 with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102, 85, 68, 51, 34, 17] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedRead, configuration := [0], bytes := [9, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 102, 85, 68, 51, 34, 17] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, wordOfBytesHOL8, setByteHOL8, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_store_size256
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 9 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 8)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedWrite ∧ configuration = [0] ∧ input = [136, 119, 102, 85, 68, 51, 34, 17, 9, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17, 9, 0, 0, 0, 0, 0, 0, 0] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemStore 0 (.addr 2 0) start 256 with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102, 85, 68, 51, 34, 17, 9, 0, 0, 0, 0, 0, 0, 0] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedWrite, configuration := [0], bytes := [136, 119, 102, 85, 68, 51, 34, 17, 9, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 102, 85, 68, 51, 34, 17, 9, 0, 0, 0, 0, 0, 0, 0] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemStore, sharedMemoryWordBytes, addrValue, incPc, decClock, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_shared_load_address_wrap
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Unit Nat) :
    let start := { s with
      regs := (fun r => if r=2 then .word 18446744073709551615 else if r=0 then .word 1234605616436508552 else .word 99)
      sharedMemDomain := fun a => decide (a = 0)
      ffi := initialHolFfiState (fun name _host configuration input => if name = .sharedMem .mappedRead ∧ configuration = [0] ∧ input = [0, 0, 0, 0, 0, 0, 0, 0] then .ret (_host+1) [136, 119, 102, 85, 68, 51, 34, 17] else .final .diverged) 10
      pc := 3
      clock := 5
      failed := true
      be := false }
    match shareMemOp .load 0 (.addr 2 1) start with
    | some (.ret ffi bytes, t) => bytes = [136, 119, 102, 85, 68, 51, 34, 17] ∧ ffi.ffiState = 11 ∧ ffi.ioEvents = [{ name := .sharedMem .mappedRead, configuration := [0], bytes := [0, 0, 0, 0, 0, 0, 0, 0].zip [136, 119, 102, 85, 68, 51, 34, 17] }] ∧ t.ffi = ffi ∧ t.regs 0 = .word 1234605616436508552 ∧ t.regs 1 = .word 99 ∧ t.pc = 4 ∧ t.clock = 4 ∧ t.failed = true
    | _ => False := by
  simp +decide [shareMemOp, shareMemLoad, sharedMemoryWordBytes, addrValue, callFFIHOL, initialHolFfiState, wordOfBytesHOL8, setByteHOL8, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

end Flapjack.Test.LabSemSharedMemoryParity
