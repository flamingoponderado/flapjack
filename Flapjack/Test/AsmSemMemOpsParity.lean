import Flapjack.Compiler.Encoders.AsmSem.MemOps

/-! Kernel replay of `scripts/hol-probes/asm_sem_mem_ops_probe.out`: the original HOL
`mem_load`, `mem_store` and `mem_op` results on an 8-bit state, with the positive `LOG2` values
proved from `LOG_UNIQUE` as in the probe; the zero-count row keeps `LOG2 0` unconstrained on both
sides. -/
set_option maxRecDepth 16384

namespace Flapjack.Test.AsmSemMemOpsParity
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem

private def st : AsmState 8 :=
  { regs := fun r => if r = 3 then 0xAB else 0
    fpRegs := fun _ => 0
    mem := fun x => if x = 0 then 0x11 else if x = 1 then 0x22 else 0x33
    memDomain := fun x => x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3
    pc := 0, lr := 0, align := 0, be := false, failed := false }

private theorem lg1 : holLOG2 1 = 0 := holLOG_UNIQUE 2 1 0 ⟨by decide, by decide⟩
private theorem lg2 : holLOG2 2 = 1 := holLOG_UNIQUE 2 2 1 ⟨by decide, by decide⟩
private theorem lg4 : holLOG2 4 = 2 := holLOG_UNIQUE 2 4 2 ⟨by decide, by decide⟩

local macro "mo_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) [memLoad, memStore, memOp, readMemWord, writeMemWord,
    addrHOL, readReg, updReg, updMem, assertState, readMem, st, lg1, lg2, lg4, holAligned,
    holAlign_eq_div])

-- mo_ld2_le_reg=17w
example : (memLoad 2 5 (.addr 0 (0 : BitVec 8)) st).regs 5 = 17 := by mo_simp
-- mo_ld2_le_ok=F
example : (memLoad 2 5 (.addr 0 (0 : BitVec 8)) st).failed = false := by mo_simp
-- mo_ld2_be_reg=34w
example : (memLoad 2 5 (.addr 0 (0 : BitVec 8)) { st with be := true }).regs 5 = 34 := by mo_simp
-- mo_ld2_misaligned=T
example : (memLoad 2 5 (.addr 0 (1 : BitVec 8)) st).failed = true := by mo_simp
-- mo_ld2_dom=T
example : (memLoad 2 5 (.addr 0 (6 : BitVec 8)) st).failed = true := by mo_simp
-- mo_ld0_reg=0w
example : (memLoad 0 5 (.addr 0 (1 : BitVec 8)) st).regs 5 = 0 := by mo_simp
-- mo_ld0_failed=(mem_load 0 5 (Addr 0 1w) <|...|>).failed ⇔ ¬aligned (LOG2 0) 1w
example : (memLoad 0 5 (.addr 0 (1 : BitVec 8)) st).failed = !(holAligned (holLOG2 0) (1 : BitVec 8)) := by
  simp [memLoad, readMemWord, addrHOL, readReg, updReg, assertState, st]
-- mo_st1_mem=171w
example : (memStore 1 3 (.addr 0 (2 : BitVec 8)) st).mem 2 = 171 := by mo_simp
-- mo_st1_ok=F
example : (memStore 1 3 (.addr 0 (2 : BitVec 8)) st).failed = false := by mo_simp
-- mo_st2_misaligned=T
example : (memStore 2 3 (.addr 0 (1 : BitVec 8)) st).failed = true := by mo_simp
-- mo_op_load=34w
example : (memOp .load 5 (.addr 0 (1 : BitVec 8)) st).regs 5 = 34 := by mo_simp
-- mo_op_load32_failed=F
example : (memOp .load32 5 (.addr 0 (0 : BitVec 8)) st).failed = false := by mo_simp
-- mo_op_store8_mem=171w
example : (memOp .store8 3 (.addr 0 (1 : BitVec 8)) st).mem 1 = 171 := by mo_simp
-- mo_op_load16_reg=51w
example : (memOp .load16 5 (.addr 0 (2 : BitVec 8)) st).regs 5 = 51 := by mo_simp

end Flapjack.Test.AsmSemMemOpsParity
