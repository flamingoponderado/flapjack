import Flapjack.RiscV.L3.Step.LoadStep
import Flapjack.RiscV.L3.Defs.WordArithmetic
import Flapjack.RiscV.L3.Defs.UpperJump

/-! Evaluated original `riscv_stepScript.sml` word-arithmetic step theorems
(`Skip` line 637, `ADDIW` line 838; `ADDW`/`SUBW` are absent on riscv-mi).
`ADDIW` keeps the original RV32-exclusion and invalid-selector mode hypotheses
together with the destination hypothesis, and computes on the low 32 bits before
sign-extending the result to 64 bits.  `Skip` is the unchanged source counter. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

theorem dfnSkip (s : riscv_state) : Skip s = s.c_Skip s.procID := rfl

theorem dfnADDIW (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'ADDIW» (rd, (rs1, imm)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if rs1 = 0 then
            BitVec.signExtend 64 (holWordExtract 32 31 0 (BitVec.signExtend 64 imm))
           else
            BitVec.signExtend 64 (holWordExtract 32 31 0 (s.c_gpr s.procID rs1 + BitVec.signExtend 64 imm)))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'ADDIW»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte, «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> simp_all [holWordExtract]

theorem dfnADDIWNop (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'ADDIW» (rd, (rs1, imm)) s = s := by
  simp only [«dfn'ADDIW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

end Flapjack.RiscV.L3.Step
