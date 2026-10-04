import Flapjack.RiscV.L3.Defs.Multiply
import Flapjack.RiscV.L3.Defs.Divide

/-! Evaluated original `riscv_stepScript.sml` integer multiply/divide instruction
theorems for four full-width forms (`MUL`, `DIV`, `REM`, `REMU`, lines
874-886) over the literal native equations and the hex-equivalent all-ones
zero-divisor result.  Each write theorem keeps the original destination
hypothesis `rd <> 0w`; the remainder/quotient forms preserve the explicit zero
divisor branches. The evaluated `DIVU` and word-form equations remain separate
porting work; this module does not claim those results. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

theorem dfnMUL (rd rs1 rs2 : BitVec 5) (s : riscv_state) (hrd : rd ≠ 0) :
    «dfn'MUL» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          ((if rs1 = 0 then 0 else s.c_gpr s.procID rs1) *
           (if rs2 = 0 then 0 else s.c_gpr s.procID rs2))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'MUL», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    by_cases hz : s.c_gpr s.procID rs2 = 0 <;> simp_all [beq_iff_eq]

theorem dfnDIV (rd rs1 rs2 : BitVec 5) (s : riscv_state) (hrd : rd ≠ 0) :
    «dfn'DIV» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (if rs2 = 0 then True else s.c_gpr s.procID rs2 = 0)
           then BitVec.signExtend 64 (BitVec.ofNat 1 1)
           else BitVec.sdiv (if rs1 = 0 then 0 else s.c_gpr s.procID rs1)
             (if rs2 = 0 then 0 else s.c_gpr s.procID rs2))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'DIV», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    by_cases hz : s.c_gpr s.procID rs2 = 0 <;> simp_all [beq_iff_eq]

theorem dfnREM (rd rs1 rs2 : BitVec 5) (s : riscv_state) (hrd : rd ≠ 0) :
    «dfn'REM» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (if rs2 = 0 then True else s.c_gpr s.procID rs2 = 0)
           then (if rs1 = 0 then 0 else s.c_gpr s.procID rs1)
           else BitVec.srem (if rs1 = 0 then 0 else s.c_gpr s.procID rs1)
             (if rs2 = 0 then 0 else s.c_gpr s.procID rs2))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'REM», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    by_cases hz : s.c_gpr s.procID rs2 = 0 <;> simp_all [beq_iff_eq]

theorem dfnREMU (rd rs1 rs2 : BitVec 5) (s : riscv_state) (hrd : rd ≠ 0) :
    «dfn'REMU» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (if rs2 = 0 then True else s.c_gpr s.procID rs2 = 0)
           then (if rs1 = 0 then 0 else s.c_gpr s.procID rs1)
           else BitVec.umod (if rs1 = 0 then 0 else s.c_gpr s.procID rs1)
             (if rs2 = 0 then 0 else s.c_gpr s.procID rs2))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'REMU», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    by_cases hz : s.c_gpr s.procID rs2 = 0 <;> simp_all [beq_iff_eq]

private theorem ite_holUpdate_gpr (C : Prop) [Decidable C] (s : riscv_state)
    (rd : BitVec 5) (v1 v2 : BitVec 64) :
    (if C then
        { s with c_gpr := holUpdate s.procID (holUpdate rd v1 (s.c_gpr s.procID)) s.c_gpr }
     else
        { s with c_gpr := holUpdate s.procID (holUpdate rd v2 (s.c_gpr s.procID)) s.c_gpr }) =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd (if C then v1 else v2) (s.c_gpr s.procID))
          s.c_gpr } := by
  by_cases h : C <;> simp_all

theorem dfnDIVU (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'DIVU» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (if rs2 = 0 then True
               else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0 then
                 BitVec.setWidth 64 (holWordExtract 32 31 0 (s.c_gpr s.procID rs2)) = 0
               else s.c_gpr s.procID rs2 = 0)
           then BitVec.signExtend 64 (BitVec.ofNat 1 1)
           else BitVec.udiv
             (if rs1 = 0 then 0
              else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0 then
                BitVec.setWidth 64 (holWordExtract 32 31 0 (s.c_gpr s.procID rs1))
              else s.c_gpr s.procID rs1)
             (if rs2 = 0 then 0
              else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0 then
                BitVec.setWidth 64 (holWordExtract 32 31 0 (s.c_gpr s.procID rs2))
              else s.c_gpr s.procID rs2))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'DIVU»]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, GPR, gpr,
      ne_eq, «write'GPR», «write'gpr», holWordExtract, ite_holUpdate_gpr] <;>
    by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;> simp_all

theorem dfnDIVUNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'DIVU» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'DIVU», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

theorem dfnMULNop (rd rs1 rs2 : BitVec 5) (s : riscv_state) (hrd : rd = 0) :
    «dfn'MUL» (rd, (rs1, rs2)) s = s := by
  simp [«dfn'MUL», «write'GPR», hrd]

theorem dfnDIVNop (rd rs1 rs2 : BitVec 5) (s : riscv_state) (hrd : rd = 0) :
    «dfn'DIV» (rd, (rs1, rs2)) s = s := by
  simp [«dfn'DIV», «write'GPR», hrd]

theorem dfnREMNop (rd rs1 rs2 : BitVec 5) (s : riscv_state) (hrd : rd = 0) :
    «dfn'REM» (rd, (rs1, rs2)) s = s := by
  simp [«dfn'REM», «write'GPR», hrd]

theorem dfnREMUNop (rd rs1 rs2 : BitVec 5) (s : riscv_state) (hrd : rd = 0) :
    «dfn'REMU» (rd, (rs1, rs2)) s = s := by
  simp [«dfn'REMU», «write'GPR», hrd]

end Flapjack.RiscV.L3.Step
