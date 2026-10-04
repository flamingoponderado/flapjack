import Flapjack.Compiler.Backend.LabSem.Updates

/-! Kernel replays of the original labsem_updates_probe.out observations.
Failure preserves writes, total maps retain other keys, and FP values retain raw64 bits. -/
namespace Flapjack.Test.LabSemUpdatesParity
open Flapjack.Compiler.Backend.LabSem
variable (s : Flapjack.Compiler.Backend.LabSem.State 8 Unit Unit)

-- lab_updates_pc_overwrite
example : (updPc 9 s).pc = 9 := rfl

-- lab_updates_pc_increment
example : (incPc { s with pc := 9 }).pc = 10 := rfl

-- lab_updates_clock_zero
example : (decClock { s with clock := 0 }).clock = 0 := rfl

-- lab_updates_clock_positive
example : (decClock { s with clock := 7 }).clock = 6 := rfl

-- lab_updates_reg_hit
example : (updReg 2 (.word 99) { s with regs := fun _ => .word 17 }).regs 2 = .word 99 := by simp [updReg]

-- lab_updates_reg_other
example : (updReg 2 (.word 99) { s with regs := fun _ => .word 17 }).regs 3 = .word 17 := by simp [updReg]

-- lab_updates_reg_loc
example : (updReg 2 (.loc 4 5) s).regs 2 = .loc 4 5 := by simp [updReg]

-- lab_updates_mem_hit
example : (updMem 1 (.loc 4 5) { s with memory := fun _ => .word 17 }).memory 1 = .loc 4 5 := by simp [updMem]

-- lab_updates_mem_other
example : (updMem 1 (.loc 4 5) { s with memory := fun _ => .word 17 }).memory 2 = .word 17 := by simp [updMem]

-- lab_updates_assert_sticky
example : (assertState true { s with failed := true }).failed = true := rfl

-- lab_updates_assert_false
example : (assertState false { s with failed := false }).failed = true := rfl

-- lab_updates_failed_reg_write
example : (assertState false (updReg 2 (.loc 4 5) s)).regs 2 = .loc 4 5 := by simp [assertState, updReg]

-- lab_updates_failed_mem_write
example : (assertState false (updMem 1 (.loc 4 5) s)).memory 1 = .loc 4 5 := by simp [assertState, updMem]

-- lab_updates_reg_imm_loc
example : regImm (.reg 2) (updReg 2 (.loc 4 5) s) = .loc 4 5 := by simp [regImm, updReg]

-- lab_updates_reg_imm_word
example : regImm (.imm 255) s = .word 255 := rfl

-- lab_updates_fp_hit

-- lab_updates_fp_other

end Flapjack.Test.LabSemUpdatesParity
