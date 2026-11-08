import Flapjack.RiscV.L3.Defs.SetLess
import Flapjack.RiscV.L3.Step.ComparisonMode

namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3
set_option autoImplicit false

/-- Original generated SLTI_NOP companion at source839. Both original
hypotheses are retained: destination zero and ArchBase exclusion. The entire
native state is unchanged, with arbitrary source register and immediate.
Only word/register/mode operations occur; no real arithmetic assumption. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLTI_NOP"]
theorem dfnSltINop (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state)
    (h : rd = 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLTI» (rd, rs1, imm) s = s := by
  subst rd
  simp only [«dfn'SLTI», comparison_mode s arch]
  simp [«write'GPR»]

/-- Original generated SLTIU_NOP companion at source840, with the same two
original hypotheses and unrestricted word5 source/word12 immediate. Whole
native state equality is retained; no real arithmetic assumption. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLTIU_NOP"]
theorem dfnSltIUNop (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state)
    (h : rd = 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLTIU» (rd, rs1, imm) s = s := by
  subst rd
  simp only [«dfn'SLTIU», comparison_mode s arch]
  simp [«write'GPR»]

end Flapjack.RiscV.L3.Step
