import Flapjack.Compiler.Encoders.AsmSem.Memory

/-! Kernel regressions for the independent byte-shift count in source memory.
These concrete observations are Flapjack regression infrastructure, not separate
HOL theorem ports. The original observations are captured in asm_memory_shift_probe.out.
The address width is eight; result/value widths remain independent. -/
namespace Flapjack.Compiler.Encoders.AsmSem.MemoryByteShift
open Flapjack Flapjack.Compiler.Encoders.AsmSem
private def sample : AsmState 8 :=
 {regs := fun _ => 0, fpRegs := fun _ => 0, mem := fun a => if a = 1 then 1 else 0,
  memDomain := fun _ => True, pc := 0, lr := 0, align := 0, be := false, failed := false}

theorem read_width_1 : (readMemWord (resultWidth := 1) 0 2 sample).1 = 0 := by
  simp [readMemWord, readMem, sample, assertState]

theorem write_width_1 :
    (writeMemWord (valueWidth := 1) 0 2 1 sample).mem 0 = 1 ∧
    (writeMemWord (valueWidth := 1) 0 2 1 sample).mem 1 = 0 ∧
    (writeMemWord (valueWidth := 1) 0 2 1 sample).failed = false := by
  simp [writeMemWord, updMem, sample, assertState]

theorem read_width_2 : (readMemWord (resultWidth := 2) 0 2 sample).1 = 0 := by
  simp [readMemWord, readMem, sample, assertState]

theorem write_width_2 :
    (writeMemWord (valueWidth := 2) 0 2 1 sample).mem 0 = 1 ∧
    (writeMemWord (valueWidth := 2) 0 2 1 sample).mem 1 = 0 ∧
    (writeMemWord (valueWidth := 2) 0 2 1 sample).failed = false := by
  simp [writeMemWord, updMem, sample, assertState]

theorem read_width_3 : (readMemWord (resultWidth := 3) 0 2 sample).1 = 0 := by
  simp [readMemWord, readMem, sample, assertState]

theorem write_width_3 :
    (writeMemWord (valueWidth := 3) 0 2 1 sample).mem 0 = 1 ∧
    (writeMemWord (valueWidth := 3) 0 2 1 sample).mem 1 = 0 ∧
    (writeMemWord (valueWidth := 3) 0 2 1 sample).failed = false := by
  simp [writeMemWord, updMem, sample, assertState]

theorem read_width_64 : (readMemWord (resultWidth := 64) 0 2 sample).1 = 256 := by
  simp [readMemWord, readMem, sample, assertState]

theorem write_width_64 :
    (writeMemWord (valueWidth := 64) 0 2 1 sample).mem 0 = 1 ∧
    (writeMemWord (valueWidth := 64) 0 2 1 sample).mem 1 = 0 ∧
    (writeMemWord (valueWidth := 64) 0 2 1 sample).failed = false := by
  simp [writeMemWord, updMem, sample, assertState]

end Flapjack.Compiler.Encoders.AsmSem.MemoryByteShift
