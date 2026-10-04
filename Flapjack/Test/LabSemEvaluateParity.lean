import Flapjack.Compiler.Backend.LabSem.Evaluate

/-! Whole native executions paired with original labSem evaluate_def.
The source state is arbitrary outside fields fixed by each original probe. -/
set_option maxRecDepth 16384

namespace Flapjack.Test.LabSemEvaluateParity
open Flapjack Flapjack.Compiler.Backend.LabSem

-- lab_eval_clock_zero
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 0
      code := [{ sectionId := 1, lines := [.labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.timeOut,t) => t = start
    | _ => False := by
  simp +decide [evaluate]
    <;> decide +kernel

-- lab_eval_halt_success
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.halt .success,t) => t = start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux]
    <;> decide +kernel

-- lab_eval_halt_resource
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 1 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.halt .resourceLimitHit,t) => t = start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux]
    <;> decide +kernel

-- lab_eval_halt_loc_error
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .loc 3 4 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t = start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux]
    <;> decide +kernel

-- lab_eval_halt_failed_still_success
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := true
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.halt .success,t) => t = start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux]
    <;> decide +kernel

-- lab_eval_fetch_empty
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := []
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t = start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux]
    <;> decide +kernel

-- lab_eval_fetch_beyond
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 9
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t = start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux]
    <;> decide +kernel

-- lab_eval_unsupported_asmi
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.asmi (.jump 0)) [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t = start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux]
    <;> decide +kernel

-- lab_eval_const_then_halt
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 5 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.asmi (.inst (.const 0 0))) [] 7, .labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.halt .success,t) => t.regs 0 = .word 0 ∧ t.pc=1 ∧ t.clock=1
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, asmInst, updReg, incPc, decClock]
    <;> decide +kernel

-- lab_eval_skip_timeout
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 1
      code := [{ sectionId := 1, lines := [.asm (.asmi (.inst (.skip))) [] 7, .labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.timeOut,t) => t.pc=1 ∧ t.clock=0
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, asmInst, incPc, decClock]
    <;> decide +kernel

-- lab_eval_failed_skip_rollback
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := true
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.asmi (.inst (.skip))) [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, asmInst]
    <;> decide +kernel

-- lab_eval_div_failure_rollback
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 5 else if r=2 then .word 99 else if r=3 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.asmi (.inst (.arith (.div 0 2 3)))) [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start ∧ t.regs 0=.word 5 ∧ t.failed=false
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, asmInst, arithUpd, assertState, updReg]
    <;> decide +kernel

-- lab_eval_store_failure_rollback
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .loc 7 8 else if r=2 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.asmi (.inst (.mem .store 0 (.addr 2 1)))) [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start ∧ t.memory 1=.word 52 ∧ t.failed=false
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, asmInst, memOp, memStore, assertState, updMem, addrValue]
    <;> decide +kernel

-- lab_eval_fp_neg_then_halt
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.asmi (.jumpReg 2)) [] 7, .label 1 9 7, .labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.halt .success,t) => t.pc=1 ∧ t.clock=1
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, updPc, decClock, locToPc]
    <;> decide +kernel

-- lab_eval_jumpreg_word_error
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.asmi (.jumpReg 2)) [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux]
    <;> decide +kernel

-- lab_eval_jumpreg_missing_error
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .loc 8 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.asmi (.jumpReg 2)) [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc]
    <;> decide +kernel

-- lab_eval_cbw_then_halt
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .word 33 else if r=3 then .word 999 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.cbw 2 3) [] 7, .labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.halt .success,t) => t.codeBuffer.buffer=[10,231] ∧ t.codeBuffer.spaceLeft=1 ∧ t.clock=1
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, incPc, decClock, wordSemBufferWrite]
    <;> decide +kernel

-- lab_eval_cbw_timeout
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .word 33 else if r=3 then .word 999 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 1
      code := [{ sectionId := 1, lines := [.asm (.cbw 2 3) [] 7, .labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.timeOut,t) => t.codeBuffer.buffer=[10,231] ∧ t.pc=1 ∧ t.clock=0
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, incPc, decClock, wordSemBufferWrite]
    <;> decide +kernel

-- lab_eval_cbw_address_error
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .word 34 else if r=3 then .word 999 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.cbw 2 3) [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, wordSemBufferWrite]
    <;> decide +kernel

-- lab_eval_cbw_space_error
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .word 33 else if r=3 then .word 999 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.cbw 2 3) [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 0 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, wordSemBufferWrite]
    <;> decide +kernel

-- lab_eval_cbw_loc_error
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .loc 1 9 else if r=3 then .word 999 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.cbw 2 3) [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux]
    <;> decide +kernel

-- lab_eval_locvalue_success
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.locValue 2 (.lab 1 9)) 0 [] 7, .label 1 9 7, .labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.halt .success,t) => t.regs 2=.loc 1 9 ∧ t.pc=1 ∧ t.clock=1
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, updReg, incPc, decClock, locToPc, getPcValue, labToLoc]
    <;> decide +kernel

-- lab_eval_locvalue_missing
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.locValue 2 (.lab 8 9)) 0 [] 7, .labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, getPcValue]
    <;> decide +kernel

-- lab_eval_jump_success
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.jump (.lab 1 9)) 0 [] 7, .asm (.asmi (.inst (.const 0 1))) [] 7, .label 1 9 7, .labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.halt .success,t) => t.pc=2 ∧ t.clock=1 ∧ t.regs 0=.word 0
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, updPc, decClock, locToPc, getPcValue]
    <;> decide +kernel

-- lab_eval_jump_missing
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.jump (.lab 8 9)) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, getPcValue]
    <;> decide +kernel

-- lab_eval_jump_self_timeout
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 3
      code := [{ sectionId := 1, lines := [.labAsm (.jump (.lab 1 0)) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.timeOut,t) => t.pc=0 ∧ t.clock=0
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, updPc, decClock, locToPc, getPcValue]
    <;> decide +kernel

-- lab_eval_jumpcmp_true
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .word 3 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 3
      code := [{ sectionId := 1, lines := [.labAsm (.jumpCmp .equal 2 (.imm 3) (.lab 1 9)) 0 [] 7, .asm (.asmi (.inst (.const 0 1))) [] 7, .label 1 9 7, .labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.halt .success,t) => t.pc=2 ∧ t.clock=2 ∧ t.regs 0=.word 0
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, regImm, updPc, decClock, locToPc, getPcValue, wordSemWordCmp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    <;> decide +kernel

-- lab_eval_jumpcmp_false
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .word 4 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 3
      code := [{ sectionId := 1, lines := [.labAsm (.jumpCmp .equal 2 (.imm 3) (.lab 1 9)) 0 [] 7, .asm (.asmi (.inst (.const 0 1))) [] 7, .label 1 9 7, .labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.halt .resourceLimitHit,t) => t.pc=2 ∧ t.clock=1 ∧ t.regs 0=.word 1
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, asmInst, regImm, updReg, incPc, decClock, wordSemWordCmp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    <;> decide +kernel

-- lab_eval_jumpcmp_true_missing
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .word 3 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.jumpCmp .equal 2 (.imm 3) (.lab 8 9)) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, regImm, locToPc, getPcValue, wordSemWordCmp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    <;> decide +kernel

-- lab_eval_jumpcmp_false_missing_ignored
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .word 4 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.jumpCmp .equal 2 (.imm 3) (.lab 8 9)) 0 [] 7, .labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.halt .success,t) => t.pc=1 ∧ t.clock=1
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, regImm, incPc, decClock, wordSemWordCmp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    <;> decide +kernel

-- lab_eval_jumpcmp_loc_test
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .loc 4 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.jumpCmp .test 2 (.imm 1) (.lab 1 9)) 0 [] 7, .asm (.asmi (.inst (.const 0 1))) [] 7, .label 1 9 7, .labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.halt .success,t) => t.pc=2 ∧ t.clock=1
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, regImm, updPc, decClock, locToPc, getPcValue, wordSemWordCmp]
    <;> decide +kernel

-- lab_eval_jumpcmp_loc_error
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .loc 4 3 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.jumpCmp .test 2 (.imm 1) (.lab 1 9)) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, regImm, wordSemWordCmp]
    <;> decide +kernel

-- lab_eval_call_return
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 3
      code := [{ sectionId := 1, lines := [.labAsm (.call (.lab 2 0)) 0 [] 7, .label 1 9 7, .labAsm (.halt) 0 [] 7] }, { sectionId := 2, lines := [.asm (.asmi (.jumpReg 4)) [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.halt .success,t) => t.regs 4=.loc 1 9 ∧ t.pc=1 ∧ t.clock=1
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, updReg, updPc, decClock, locToPc, getPcValue, getRetLoc, getLabAfter, nextLabel]
    <;> decide +kernel

-- lab_eval_call_missing_target
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.call (.lab 8 0)) 0 [] 7, .label 1 9 7, .labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, getPcValue]
    <;> decide +kernel

-- lab_eval_call_missing_return
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.call (.lab 2 0)) 0 [] 7] }, { sectionId := 2, lines := [.labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, getPcValue, getRetLoc, getLabAfter, nextLabel]
    <;> decide +kernel

-- lab_eval_shared_domain_error
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => false
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.shareMem .load16 5 (.addr 2 0)) [] 7, .labAsm (.halt) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, addrValue, shareMemOp, shareMemLoad]
    <;> decide +kernel

-- lab_eval_shared_loc_address_error
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.shareMem .load16 5 (.addr 2 0)) [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, addrValue, shareMemOp, shareMemLoad, sharedMemoryWordBytes, callFFIHOL, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_eval_shared_load16_identity
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.shareMem .load16 5 (.addr 2 0)) [] 7, .labAsm (.halt) 0 [] 7] }]
      ffi := initialHolFfiState (fun _name host _cfg bytes => .ret (host+1) bytes) 10
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4
      ioRegs := fun n _name r => if r=1 then some (if n=0 then 40 else 41) else none
      ccRegs := fun n r => if r=1 then some (BitVec.ofNat 64 (n+90)) else none
      ioFpRegs := fun n _r => (if n=0 then 102 else 1102)
      ccFpRegs := fun n r => BitVec.ofNat 64 (n*1000+r+200)
      compile := fun _cfg _prog => none
      compileOracle := fun _ => (0,[]) }
    match evaluate start with
    | (.halt .success,t) => t.pc=1 ∧ t.clock=1 ∧ t.regs 5=.word 0 ∧ t.regs 1=.word 5 ∧ t.fpRegs 2=9223372036854775808 ∧ t.ioRegs 0 (.sharedMem .mappedRead) 1=some 41 ∧ t.ioFpRegs 0 2=1102 ∧ t.ffi.ffiState=11 ∧ t.ffi.ioEvents=[{ name := .sharedMem .mappedRead, configuration := [2], bytes := [0, 0, 0, 0, 0, 0, 0, 0].zip [0, 0, 0, 0, 0, 0, 0, 0] }]
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, addrValue, shareMemOp, shareMemLoad, sharedMemoryWordBytes, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_eval_shared_load16_final
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.shareMem .load16 5 (.addr 2 0)) [] 7, .labAsm (.halt) 0 [] 7] }]
      ffi := initialHolFfiState (fun _name _host _cfg _bytes => .final .diverged) 10
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4
      ioRegs := fun n _name r => if r=1 then some (if n=0 then 40 else 41) else none
      ccRegs := fun n r => if r=1 then some (BitVec.ofNat 64 (n+90)) else none
      ioFpRegs := fun n _r => (if n=0 then 102 else 1102)
      ccFpRegs := fun n r => BitVec.ofNat 64 (n*1000+r+200)
      compile := fun _cfg _prog => none
      compileOracle := fun _ => (0,[]) }
    match evaluate start with
    | (.halt (.ffiOutcome event),t) => t=start ∧ event.name=.sharedMem .mappedRead ∧ event.configuration=[2] ∧ event.bytes=[0, 0, 0, 0, 0, 0, 0, 0] ∧ event.outcome=.diverged
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, addrValue, shareMemOp, shareMemLoad, sharedMemoryWordBytes, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_eval_shared_load16_badlength
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.shareMem .load16 5 (.addr 2 0)) [] 7, .labAsm (.halt) 0 [] 7] }]
      ffi := initialHolFfiState (fun _name host _cfg _bytes => .ret (host+1) []) 10
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4
      ioRegs := fun n _name r => if r=1 then some (if n=0 then 40 else 41) else none
      ccRegs := fun n r => if r=1 then some (BitVec.ofNat 64 (n+90)) else none
      ioFpRegs := fun n _r => (if n=0 then 102 else 1102)
      ccFpRegs := fun n r => BitVec.ofNat 64 (n*1000+r+200)
      compile := fun _cfg _prog => none
      compileOracle := fun _ => (0,[]) }
    match evaluate start with
    | (.halt (.ffiOutcome event),t) => t=start ∧ event.name=.sharedMem .mappedRead ∧ event.configuration=[2] ∧ event.bytes=[0, 0, 0, 0, 0, 0, 0, 0] ∧ event.outcome=.failed
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, addrValue, shareMemOp, shareMemLoad, sharedMemoryWordBytes, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_eval_shared_store16_return
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=2 then .word 0 else if r=5 then .word 513 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.asm (.shareMem .store16 5 (.addr 2 0)) [] 7, .labAsm (.halt) 0 [] 7] }]
      ffi := initialHolFfiState (fun _name host _cfg bytes => .ret (host+1) bytes) 10
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4
      ioRegs := fun n _name r => if r=1 then some (if n=0 then 40 else 41) else none
      ccRegs := fun n r => if r=1 then some (BitVec.ofNat 64 (n+90)) else none
      ioFpRegs := fun n _r => (if n=0 then 102 else 1102)
      ccFpRegs := fun n r => BitVec.ofNat 64 (n*1000+r+200)
      compile := fun _cfg _prog => none
      compileOracle := fun _ => (0,[]) }
    match evaluate start with
    | (.halt .success,t) => t.regs 5=.word 513 ∧ t.pc=1 ∧ t.clock=1 ∧ t.ioRegs 0 (.sharedMem .mappedWrite) 1=some 41 ∧ t.ffi.ffiState=11 ∧ t.ffi.ioEvents=[{ name := .sharedMem .mappedWrite, configuration := [2], bytes := [1, 2, 0, 0, 0, 0, 0, 0, 0, 0].zip [1, 2, 0, 0, 0, 0, 0, 0, 0, 0] }]
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, addrValue, incPc, decClock, shareMemOp, shareMemStore, sharedMemoryWordBytes, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL]
    <;> decide +kernel

-- lab_eval_install_operands_error
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.install) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux]
    <;> decide +kernel

-- lab_eval_install_flush_error
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 32 else if r=1 then .word 99 else if r=4 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.install) 0 [] 7, .label 1 9 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, wordSemBufferFlush]
    <;> decide +kernel

-- lab_eval_install_return_missing
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 32 else if r=1 then .word 33 else if r=4 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.install) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, wordSemBufferFlush]
    <;> decide +kernel

-- lab_eval_install_compile_none
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 32 else if r=1 then .word 33 else if r=4 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.install) 0 [] 7, .label 1 9 7] }]
      ffi := initialHolFfiState (fun _name host _cfg bytes => .ret (host+1) bytes) 10
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4
      ioRegs := fun n _name r => if r=1 then some (if n=0 then 40 else 41) else none
      ccRegs := fun n r => if r=1 then some (BitVec.ofNat 64 (n+90)) else none
      ioFpRegs := fun n _r => (if n=0 then 102 else 1102)
      ccFpRegs := fun n r => BitVec.ofNat 64 (n*1000+r+200)
      compile := fun _cfg _prog => none
      compileOracle := fun _ => (0,[]) }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, wordSemBufferFlush, initialHolFfiState]
    <;> decide +kernel

-- lab_eval_ffi_operand_error
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.callFFI (Flapjack.Basis.Pure.MlString.MlString.implode [113])) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux]
    <;> decide +kernel

-- lab_eval_ffi_domain_error
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=1 then .word 1 else if r=2 then .word 8 else if r=3 then .word 1 else if r=4 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => false
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.callFFI (Flapjack.Basis.Pure.MlString.MlString.implode [113])) 0 [] 7, .label 1 9 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, readBytearrayWordHOL, memLoadByteAuxExact]
    <;> decide +kernel

-- lab_eval_ffi_return_missing
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=1 then .word 0 else if r=2 then .word 8 else if r=3 then .word 0 else if r=4 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.callFFI (Flapjack.Basis.Pure.MlString.MlString.implode [113])) 0 [] 7] }]
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4 }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, readBytearrayWordHOL]
    <;> decide +kernel

-- lab_eval_ffi_identity
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=1 then .word 1 else if r=2 then .word 8 else if r=3 then .word 1 else if r=4 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.callFFI (Flapjack.Basis.Pure.MlString.MlString.implode [113])) 0 [] 7, .label 1 9 7, .labAsm (.halt) 0 [] 7] }]
      ffi := initialHolFfiState (fun _name host _cfg bytes => .ret (host+1) bytes) 10
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4
      ioRegs := fun n _name r => if r=1 then some (if n=0 then 40 else 41) else none
      ccRegs := fun n r => if r=1 then some (BitVec.ofNat 64 (n+90)) else none
      ioFpRegs := fun n _r => (if n=0 then 102 else 1102)
      ccFpRegs := fun n r => BitVec.ofNat 64 (n*1000+r+200)
      compile := fun _cfg _prog => none
      compileOracle := fun _ => (0,[]) }
    match evaluate start with
    | (.halt .success,t) => t.pc=1 ∧ t.clock=1 ∧ t.ffi.ffiState=11 ∧ t.regs 1=.word 40 ∧ t.regs 2=.word 8 ∧ t.fpRegs 2=102 ∧ t.ioRegs 0 (.extCall (Flapjack.Basis.Pure.MlString.MlString.implode [113])) 1=some 41 ∧ t.ioFpRegs 0 2=1102 ∧ t.memory 8=.word 52 ∧ t.ffi.ioEvents=[{ name := .extCall (Flapjack.Basis.Pure.MlString.MlString.implode [113]), configuration := [52], bytes := [52].zip [52] }]
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, callFFIHOL, initialHolFfiState, getRegValue, getByteHOL8, byteIndexHOL, readBytearrayWordHOL, memLoadByteAuxExact, writeBytearrayExact]
    <;> decide +kernel

-- lab_eval_ffi_final
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=1 then .word 1 else if r=2 then .word 8 else if r=3 then .word 1 else if r=4 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.callFFI (Flapjack.Basis.Pure.MlString.MlString.implode [113])) 0 [] 7, .label 1 9 7, .labAsm (.halt) 0 [] 7] }]
      ffi := initialHolFfiState (fun _name _host _cfg _bytes => .final .diverged) 10
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4
      ioRegs := fun n _name r => if r=1 then some (if n=0 then 40 else 41) else none
      ccRegs := fun n r => if r=1 then some (BitVec.ofNat 64 (n+90)) else none
      ioFpRegs := fun n _r => (if n=0 then 102 else 1102)
      ccFpRegs := fun n r => BitVec.ofNat 64 (n*1000+r+200)
      compile := fun _cfg _prog => none
      compileOracle := fun _ => (0,[]) }
    match evaluate start with
    | (.halt (.ffiOutcome event),t) => t=start ∧ event.name=.extCall (Flapjack.Basis.Pure.MlString.MlString.implode [113]) ∧ event.configuration=[52] ∧ event.bytes=[52] ∧ event.outcome=.diverged
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL, readBytearrayWordHOL, memLoadByteAuxExact]
    <;> decide +kernel

-- lab_eval_ffi_badlength
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 0 else if r=1 then .word 1 else if r=2 then .word 8 else if r=3 then .word 1 else if r=4 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 2
      code := [{ sectionId := 1, lines := [.labAsm (.callFFI (Flapjack.Basis.Pure.MlString.MlString.implode [113])) 0 [] 7, .label 1 9 7, .labAsm (.halt) 0 [] 7] }]
      ffi := initialHolFfiState (fun _name host _cfg _bytes => .ret (host+1) []) 10
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4
      ioRegs := fun n _name r => if r=1 then some (if n=0 then 40 else 41) else none
      ccRegs := fun n r => if r=1 then some (BitVec.ofNat 64 (n+90)) else none
      ioFpRegs := fun n _r => (if n=0 then 102 else 1102)
      ccFpRegs := fun n r => BitVec.ofNat 64 (n*1000+r+200)
      compile := fun _cfg _prog => none
      compileOracle := fun _ => (0,[]) }
    match evaluate start with
    | (.halt (.ffiOutcome event),t) => t=start ∧ event.name=.extCall (Flapjack.Basis.Pure.MlString.MlString.implode [113]) ∧ event.configuration=[52] ∧ event.bytes=[52] ∧ event.outcome=.failed
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, callFFIHOL, initialHolFfiState, getByteHOL8, byteIndexHOL, readBytearrayWordHOL, memLoadByteAuxExact]
    <;> decide +kernel

-- lab_eval_install_good
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 32 else if r=1 then .word 33 else if r=4 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 1
      code := [{ sectionId := 1, lines := [.labAsm (.install) 0 [] 7, .label 1 9 7, .asm (.asmi (.jumpReg 0)) [] 7] }]
      ffi := initialHolFfiState (fun _name host _cfg bytes => .ret (host+1) bytes) 10
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4
      ioRegs := fun n _name r => if r=1 then some (if n=0 then 40 else 41) else none
      ccRegs := fun n r => if r=1 then some (if n=0 then 90 else 91) else none
      ioFpRegs := fun n _r => (if n=0 then 102 else 1102)
      ccFpRegs := fun n _r => (if n=0 then 202 else 1202)
      compile := fun _cfg _prog => some ([10],6)
      compileOracle := fun n => ((if n=0 then 5 else 6),[{ sectionId := 7, lines := [.asm (.asmi (.inst (.const 0 0))) [] 7, .labAsm (.halt) 0 [] 7] }]) }
    match evaluate start with
    | (.timeOut,t) => t.pc=1 ∧ t.clock=0 ∧ t.regs 0=.loc 7 0 ∧ t.regs 1=.word 90 ∧ t.regs 2=.word 5 ∧ t.fpRegs 2=202 ∧ t.ccRegs 0 1=some 91 ∧ t.ccFpRegs 0 2=1202 ∧ (t.compileOracle 0).1=6 ∧ t.codeBuffer.position=33 ∧ t.codeBuffer.buffer=[] ∧ t.codeBuffer.spaceLeft=2 ∧ t.code.length=2
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, wordSemBufferFlush, initialHolFfiState, getRegValue]
    <;> decide +kernel

-- lab_eval_install_bytes
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 32 else if r=1 then .word 33 else if r=4 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 1
      code := [{ sectionId := 1, lines := [.labAsm (.install) 0 [] 7, .label 1 9 7, .asm (.asmi (.jumpReg 0)) [] 7] }]
      ffi := initialHolFfiState (fun _name host _cfg bytes => .ret (host+1) bytes) 10
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4
      ioRegs := fun n _name r => if r=1 then some (if n=0 then 40 else 41) else none
      ccRegs := fun n r => if r=1 then some (if n=0 then 90 else 91) else none
      ioFpRegs := fun n _r => (if n=0 then 102 else 1102)
      ccFpRegs := fun n _r => (if n=0 then 202 else 1202)
      compile := fun _cfg _prog => some ([99],6)
      compileOracle := fun n => ((if n=0 then 5 else 6),[{ sectionId := 7, lines := [.asm (.asmi (.inst (.const 0 0))) [] 7, .labAsm (.halt) 0 [] 7] }]) }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, wordSemBufferFlush, initialHolFfiState]
    <;> decide +kernel

-- lab_eval_install_cfg
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 32 else if r=1 then .word 33 else if r=4 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 1
      code := [{ sectionId := 1, lines := [.labAsm (.install) 0 [] 7, .label 1 9 7, .asm (.asmi (.jumpReg 0)) [] 7] }]
      ffi := initialHolFfiState (fun _name host _cfg bytes => .ret (host+1) bytes) 10
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4
      ioRegs := fun n _name r => if r=1 then some (if n=0 then 40 else 41) else none
      ccRegs := fun n r => if r=1 then some (if n=0 then 90 else 91) else none
      ioFpRegs := fun n _r => (if n=0 then 102 else 1102)
      ccFpRegs := fun n _r => (if n=0 then 202 else 1202)
      compile := fun _cfg _prog => some ([10],7)
      compileOracle := fun n => ((if n=0 then 5 else 6),[{ sectionId := 7, lines := [.asm (.asmi (.inst (.const 0 0))) [] 7, .labAsm (.halt) 0 [] 7] }]) }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, wordSemBufferFlush, initialHolFfiState]
    <;> decide +kernel

-- lab_eval_install_empty
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 32 else if r=1 then .word 33 else if r=4 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 1
      code := [{ sectionId := 1, lines := [.labAsm (.install) 0 [] 7, .label 1 9 7, .asm (.asmi (.jumpReg 0)) [] 7] }]
      ffi := initialHolFfiState (fun _name host _cfg bytes => .ret (host+1) bytes) 10
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4
      ioRegs := fun n _name r => if r=1 then some (if n=0 then 40 else 41) else none
      ccRegs := fun n r => if r=1 then some (if n=0 then 90 else 91) else none
      ioFpRegs := fun n _r => (if n=0 then 102 else 1102)
      ccFpRegs := fun n _r => (if n=0 then 202 else 1202)
      compile := fun _cfg _prog => some ([10],6)
      compileOracle := fun n => ((if n=0 then 5 else 6),[]) }
    match evaluate start with
    | (.error,t) => t=start
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, locToPc, wordSemBufferFlush, initialHolFfiState]
    <;> decide +kernel

-- lab_eval_install_execute_code
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    let start : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat := { s with
      regs := (fun r => if r=0 then .word 32 else if r=1 then .word 33 else if r=4 then .loc 1 9 else .word 5)
      memory := fun _ => .word 52
      fpRegs := fun _ => 9223372036854775808
      memDomain := fun _ => true
      sharedMemDomain := fun _ => true
      be := false
      failed := false
      pc := 0
      clock := 4
      code := [{ sectionId := 1, lines := [.labAsm (.install) 0 [] 7, .label 1 9 7, .asm (.asmi (.jumpReg 0)) [] 7] }]
      ffi := initialHolFfiState (fun _name host _cfg bytes => .ret (host+1) bytes) 10
      codeBuffer := { position := 32, buffer := [10], spaceLeft := 2 }
      ptrReg := 0
      lenReg := 1
      ptr2Reg := 2
      len2Reg := 3
      linkReg := 4
      ioRegs := fun n _name r => if r=1 then some (if n=0 then 40 else 41) else none
      ccRegs := fun n r => if r=1 then some (if n=0 then 90 else 91) else none
      ioFpRegs := fun n _r => (if n=0 then 102 else 1102)
      ccFpRegs := fun n _r => (if n=0 then 202 else 1202)
      compile := fun _cfg _prog => some ([10],6)
      compileOracle := fun n => ((if n=0 then 5 else 6),[{ sectionId := 7, lines := [.asm (.asmi (.inst (.const 0 0))) [] 7, .labAsm (.halt) 0 [] 7] }]) }
    match evaluate start with
    | (.halt .success,t) => t.pc=3 ∧ t.clock=1 ∧ t.regs 0=.word 0 ∧ t.code.length=2
    | _ => False := by
  simp +decide [evaluate, asmFetch, asmFetchAux, asmInst, updReg, updPc, incPc, decClock, locToPc, wordSemBufferFlush, initialHolFfiState, getRegValue]
    <;> decide +kernel

end Flapjack.Test.LabSemEvaluateParity
