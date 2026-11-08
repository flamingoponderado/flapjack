import Flapjack.RiscV.L3.Defs.SetLess
import Flapjack.RiscV.L3.Step.ComparisonMode

namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3
set_option autoImplicit false

/-- Full original SLT register comparison: original destination and ArchBase
hypotheses, both source-zero reads, RV32 sign extension, and whole state update.
All aliases and all remaining architecture modes are unrestricted. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLT"]
theorem dfnSlt (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (h : rd ≠ 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLT» (rd, rs1, rs2) s =
      {s with
        c_gpr := holUpdate s.procID
          (holUpdate rd
          (holV2w 64 [BitVec.slt
            (if rs1 = 0#5 then 0#64
             else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 then
               (holWordExtract 32 31 0 (s.c_gpr s.procID rs1)).signExtend 64
             else s.c_gpr s.procID rs1)
            (if rs2 = 0#5 then 0#64
             else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 then
               (holWordExtract 32 31 0 (s.c_gpr s.procID rs2)).signExtend 64
             else s.c_gpr s.procID rs2)])
          (s.c_gpr s.procID)) s.c_gpr} := by
  simp only [«dfn'SLT», comparison_mode s arch]
  by_cases zero1 : rs1 = 0#5 <;>
    by_cases zero2 : rs2 = 0#5 <;>
    by_cases mode : (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 <;>
      simp [«write'GPR», «write'gpr», GPR, gpr, h, zero1, zero2, mode,
        beq_iff_eq, holWordExtract]

/-- Full original SLTU register comparison: original destination and ArchBase
hypotheses, both source-zero reads, RV32 zero extension, and whole state update.
All aliases and all remaining architecture modes are unrestricted. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLTU"]
theorem dfnSltU (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (h : rd ≠ 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLTU» (rd, rs1, rs2) s =
      {s with
        c_gpr := holUpdate s.procID
          (holUpdate rd
          (holV2w 64 [BitVec.ult
            (if rs1 = 0#5 then 0#64
             else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 then
               (holWordExtract 32 31 0 (s.c_gpr s.procID rs1)).setWidth 64
             else s.c_gpr s.procID rs1)
            (if rs2 = 0#5 then 0#64
             else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 then
               (holWordExtract 32 31 0 (s.c_gpr s.procID rs2)).setWidth 64
             else s.c_gpr s.procID rs2)])
          (s.c_gpr s.procID)) s.c_gpr} := by
  simp only [«dfn'SLTU», comparison_mode s arch]
  by_cases zero1 : rs1 = 0#5 <;>
    by_cases zero2 : rs2 = 0#5 <;>
    by_cases mode : (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 <;>
      simp [«write'GPR», «write'gpr», GPR, gpr, h, zero1, zero2, mode,
        beq_iff_eq, holWordExtract]

/-- Original generated SLT_NOP companion. The destination-zero and
ArchBase exclusions are both retained; the two mode queries have no effect
under that original guard, and the destination write is suppressed. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLT_NOP"]
theorem dfnSltNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (h : rd = 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLT» (rd, rs1, rs2) s = s := by
  simp [«dfn'SLT», comparison_mode s arch, «write'GPR», h]

/-- Original generated SLTU_NOP companion. The destination-zero and
ArchBase exclusions are both retained; the two mode queries have no effect
under that original guard, and the destination write is suppressed. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLTU_NOP"]
theorem dfnSltUNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (h : rd = 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLTU» (rd, rs1, rs2) s = s := by
  simp [«dfn'SLTU», comparison_mode s arch, «write'GPR», h]

end Flapjack.RiscV.L3.Step
