module

public import Flapjack.RiscV.L3.Defs.SetLess
public import Flapjack.RiscV.L3.Step.ComparisonMode

@[expose] public section

namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3
set_option autoImplicit false

/-- Original evaluated SLTI equation (source839), retaining BOTH original
hypotheses, rd<>0 and ArchBase<>1. RV32 reads sign-extend the low32 bits;
source-zero, all register aliases and the full resulting native record remain.
This declaration uses only word/register/mode operations and has no inherited
real arithmetic assumption. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLTI"]
theorem dfnSltI (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state)
    (h : rd ≠ 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLTI» (rd, rs1, imm) s =
      {s with
        c_gpr := holUpdate s.procID
          (holUpdate rd
          (holV2w 64 [BitVec.slt
            (if rs1 = 0#5 then 0#64
             else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 then
               (holWordExtract 32 31 0 (s.c_gpr s.procID rs1)).signExtend 64
             else s.c_gpr s.procID rs1)
            (imm.signExtend 64)])
          (s.c_gpr s.procID)) s.c_gpr} := by
  simp only [«dfn'SLTI», comparison_mode s arch]
  by_cases zero : rs1 = 0#5 <;>
    by_cases mode : (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 <;>
      simp [«write'GPR», «write'gpr», GPR, gpr, h, zero, mode, beq_iff_eq,
        holWordExtract]

/-- Original evaluated SLTIU equation (source840), retaining BOTH original
hypotheses, rd<>0 and ArchBase<>1. RV32 reads sign-extend the low32 bits;
source-zero, all register aliases and the full resulting native record remain.
This declaration uses only word/register/mode operations and has no inherited
real arithmetic assumption. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLTIU"]
theorem dfnSltIU (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state)
    (h : rd ≠ 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLTIU» (rd, rs1, imm) s =
      {s with
        c_gpr := holUpdate s.procID
          (holUpdate rd
          (holV2w 64 [BitVec.ult
            (if rs1 = 0#5 then 0#64
             else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 then
               (holWordExtract 32 31 0 (s.c_gpr s.procID rs1)).signExtend 64
             else s.c_gpr s.procID rs1)
            (imm.signExtend 64)])
          (s.c_gpr s.procID)) s.c_gpr} := by
  simp only [«dfn'SLTIU», comparison_mode s arch]
  by_cases zero : rs1 = 0#5 <;>
    by_cases mode : (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 <;>
      simp [«write'GPR», «write'gpr», GPR, gpr, h, zero, mode, beq_iff_eq,
        holWordExtract]

end Flapjack.RiscV.L3.Step
