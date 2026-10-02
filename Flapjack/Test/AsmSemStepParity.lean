import Flapjack.Compiler.Encoders.AsmSem.Step

/-! Kernel replay of `scripts/hol-probes/asm_sem_step_probe.out`: original HOL `asm` on every
assembly clause and on instruction clauses over an 8-bit state, and the projection of
`asm_step` onto its transition and non-failure conjuncts. -/
set_option maxRecDepth 16384

namespace Flapjack.Test.AsmSemStepParity
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem

private def st : AsmState 8 :=
  { regs := fun r => if r = 3 then 0xAB else 0
    fpRegs := fun _ => 0
    mem := fun x => if x = 0 then 0x11 else if x = 1 then 0x22 else 0x33
    memDomain := fun x => x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3
    pc := 2, lr := 7, align := 0, be := false, failed := false }

private theorem lg1 : holLOG2 1 = 0 := holLOG_UNIQUE 2 1 0 ⟨by decide, by decide⟩

local macro "as_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) [asmUpd, instUpd, jumpToOffset, updPc, updReg,
    readReg, regImm, assertState, arithUpd, binopUpd, memOp, memLoad, readMemWord, addrHOL,
    readMem, wordCmpHOL, st, lg1, holAligned, holAlign_eq_div])

-- as_skip_pc=9w
example : (asmUpd (.inst .skip) (9 : BitVec 8) st).pc = 9 := by as_simp
-- as_const=(5w,9w)
example : ((asmUpd (.inst (.const 2 (5 : BitVec 8))) 9 st).regs 2,
    (asmUpd (.inst (.const 2 (5 : BitVec 8))) 9 st).pc) = (5, 9) := by as_simp
-- as_arith=172w
example : (asmUpd (.inst (.arith (.binop .add 2 3 (.imm (1 : BitVec 8))))) 9 st).regs 2 = 172 := by
  as_simp
-- as_mem=(34w,F)
example : ((asmUpd (.inst (.mem .load8 4 (.addr 0 (1 : BitVec 8)))) 9 st).regs 4,
    (asmUpd (.inst (.mem .load8 4 (.addr 0 (1 : BitVec 8)))) 9 st).failed) = (34, false) := by
  as_simp
-- as_jump=6w
example : (asmUpd (.jump (4 : BitVec 8)) 9 st).pc = 6 := by as_simp
-- as_jcmp_t=6w
example : (asmUpd (.jumpCmp .equal 3 (.imm (0xAB : BitVec 8)) 4) 9 st).pc = 6 := by as_simp
-- as_jcmp_f=9w
example : (asmUpd (.jumpCmp .equal 3 (.imm (0 : BitVec 8)) 4) 9 st).pc = 9 := by as_simp
-- as_call=(9w,6w)
example : ((asmUpd (.call (4 : BitVec 8)) 9 st).regs 7, (asmUpd (.call (4 : BitVec 8)) 9 st).pc) =
    (9, 6) := by as_simp
-- as_jumpreg_ok=(171w,F)
example : ((asmUpd (.jumpReg 3) (9 : BitVec 8) st).pc, (asmUpd (.jumpReg 3) (9 : BitVec 8) st).failed) =
    (171, false) := by as_simp
-- as_jumpreg_bad=T
example : (asmUpd (.jumpReg 3) (9 : BitVec 8) { st with align := 2 }).failed = true := by as_simp
-- as_loc=(5w,9w)
example : ((asmUpd (.loc 5 (3 : BitVec 8)) 9 st).regs 5, (asmUpd (.loc 5 (3 : BitVec 8)) 9 st).pc) =
    (5, 9) := by as_simp
-- as_step_proj=asm_step c s1 i s2 ⇒ asm i (s1.pc + n2w (LENGTH (c.encode i))) s1 = s2 ∧ ¬s2.failed
example {width : Nat} [NeZero width] (c : AsmConfigExact width) (s1 s2 : AsmState width)
    (i : HolAsm width) (h : asmStep c s1 i s2) :
    asmUpd i (s1.pc + BitVec.ofNat width (c.encode i).length) s1 = s2 ∧ ¬ s2.failed :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

end Flapjack.Test.AsmSemStepParity
