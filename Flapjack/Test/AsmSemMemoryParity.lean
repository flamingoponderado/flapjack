import Flapjack.Compiler.Encoders.AsmProps.Memory

/-! Direct original asmSem/asmProps memory-word oracle replays.  Inputs match
`scripts/hol-probes/asm_sem_mem_word_probe.out` row for row; the accessors are
the reviewed exact port and no alternate evaluator supplies the results. -/
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace Flapjack.Test.AsmSemMemoryParity
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem

private def baseState : AsmState 8 :=
  { regs := fun _ => 0
    fpRegs := fun _ => 0
    mem := fun _ => 0
    memDomain := fun x => x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3
    pc := 0, lr := 0, align := 0, be := false, failed := false }

private def memState : AsmState 8 :=
  { regs := fun _ => 0
    fpRegs := fun _ => 0
    mem := fun x => if x = 0 then 0x11 else if x = 1 then 0x22 else 0x33
    memDomain := fun _ => True
    pc := 0, lr := 0, align := 0, be := false, failed := false }

-- Original row addr.
example : addrHOL (.addr 4 (2 : BitVec 8)) baseState = 2 := by
  simp [addrHOL, readReg, baseState]

-- Original row rw_zero.
example : readMemWord (resultWidth := 8) (0 : BitVec 8) 0 baseState = ((0 : BitVec 8), baseState) := by
  rfl

-- Original row rw_le_ok.
example : ¬ (readMemWord (resultWidth := 8) (0 : BitVec 8) 4 baseState).2.failed := by
  simp +decide [readMemWord, assertState, baseState]

-- Original row rw_be_fail.
example : (readMemWord (resultWidth := 8) (0 : BitVec 8) 4 { baseState with be := true }).2.failed := by
  simp +decide [readMemWord, assertState, baseState]

-- Original row rw_fail_dom.
example : (readMemWord (resultWidth := 8) (9 : BitVec 8) 1 baseState).2.failed := by
  simp +decide [readMemWord, assertState, baseState]

-- Original row ww_zero.
example : writeMemWord (valueWidth := 8) (0 : BitVec 8) 0 (171 : BitVec 8) baseState = baseState := by
  rfl

-- Original row ww_le.
example : (writeMemWord (valueWidth := 8) (0 : BitVec 8) 1 (171 : BitVec 8) baseState).mem 0 = 171 := by
  simp +decide [writeMemWord, assertState, updMem, baseState]

-- Original row ww_le_ok.
example : ¬ (writeMemWord (valueWidth := 8) (0 : BitVec 8) 1 (171 : BitVec 8) baseState).failed := by
  simp +decide [writeMemWord, assertState, updMem, baseState]

-- Original row ww_be_fail.
example : (writeMemWord (valueWidth := 8) (0 : BitVec 8) 2 (171 : BitVec 8) { baseState with be := true }).failed := by
  simp +decide [writeMemWord, assertState, updMem, baseState]

-- Original row rw_le2.
example : (readMemWord (resultWidth := 8) (0 : BitVec 8) 2 memState).1 = 0x2211 := by
  simp +decide [readMemWord, assertState, memState]

-- Original row rw_be2.
example : (readMemWord (resultWidth := 8) (1 : BitVec 8) 2 { memState with be := true }).1 = 0x1122 := by
  simp +decide [readMemWord, assertState, memState]

-- Original row rw_wrap_ok.
example :
    ¬ (readMemWord (resultWidth := 8) (255 : BitVec 8) 4
        { memState with memDomain := fun x => x = 255 ∨ x = 0 ∨ x = 1 ∨ x = 2 }).2.failed := by
  simp +decide [readMemWord, assertState, memState]

-- Original row rw_wrap_oob.
example : (readMemWord (resultWidth := 8) (255 : BitVec 8) 4 baseState).2.failed := by
  simp +decide [readMemWord, assertState, baseState]

-- Original row rw_widen (independent result word width).
example : (readMemWord (resultWidth := 16) (0 : BitVec 8) 1 memState).1 = (0x11 : BitVec 16) := by
  simp +decide [readMemWord, assertState, memState]

-- Original row ww_widen (independent written-value word width).
example :
    (writeMemWord (valueWidth := 16) (0 : BitVec 8) 1 (0x1234 : BitVec 16) baseState).mem 0 = 0x34 := by
  simp +decide [writeMemWord, assertState, updMem, baseState]


def runChecks : IO Bool := do
  IO.println "PASS asmSem/asmProps memory-word oracle replays (15 rows)"
  pure true

end Flapjack.Test.AsmSemMemoryParity
