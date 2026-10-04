import Flapjack.RiscV.L3.Defs.UpperJump

/-! Evaluated upper-immediate instruction equations (HOL `riscv_step` upper group).

The HOL `riscv_stepScript.sml` `class` evaluator normalises each `dfn'X_def`
upper-immediate clause into an explicit record-update equation.  The
destination-write branch carries the sole hypothesis `rd <> 0w`; the generated
`X_NOP` companion carries `rd = 0w` and reduces to the unchanged state (not
taggable, since it is produced by `save_thms` rather than a literal source
declaration).  The two equations below are transcribed with the original
hypothesis and the exact normal form produced by the HOL evaluator; LUI writes
the sign-extended upper immediate and AUIPC adds the current PC. -/
namespace Flapjack.RiscV.L3.Step

open Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LUI"]
theorem dfnLui (rd : BitVec 5) (imm : BitVec 20) (s : riscv_state) (h : rd ≠ 0) :
    «dfn'LUI» (rd, imm) s =
      { s with
        c_gpr :=
          holUpdate s.procID
            (holUpdate rd
              (BitVec.signExtend 64
                (BitVec.setWidth 32 (imm ++ BitVec.ofNat 12 0)))
              (s.c_gpr s.procID))
            s.c_gpr } := by
  simp only [«dfn'LUI», «write'GPR», «write'gpr»]
  simp_all

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "AUIPC"]
theorem dfnAuiPC (rd : BitVec 5) (imm : BitVec 20) (s : riscv_state) (h : rd ≠ 0) :
    «dfn'AUIPC» (rd, imm) s =
      { s with
        c_gpr :=
          holUpdate s.procID
            (holUpdate rd
              (s.c_PC s.procID +
                BitVec.signExtend 64
                  (BitVec.setWidth 32 (imm ++ BitVec.ofNat 12 0)))
              (s.c_gpr s.procID))
            s.c_gpr } := by
  simp only [«dfn'AUIPC», «write'GPR», «write'gpr», PC]
  simp_all

end Flapjack.RiscV.L3.Step
