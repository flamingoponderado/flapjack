import Flapjack.RiscV.L3.Defs.ImmediateALU

/-! Evaluated immediate-ALU instruction equations (HOL `riscv_step` immediate group).

The HOL `riscv_stepScript.sml` `class` evaluator normalises each `dfn'X_def`
immediate clause into an explicit record-update equation.  The destination-write
branch carries the sole hypothesis `rd <> 0w`; the generated `X_NOP` companion
carries `rd = 0w` and reduces to the unchanged state (not taggable, since it is
produced by `save_thms` rather than a literal source declaration).  The four
equations below are transcribed with the original hypothesis and the exact
normal form produced by the HOL evaluator; a zero source register reads zero
and the word12 immediate is sign-extended to 64 bits. -/
namespace Flapjack.RiscV.L3.Step

open Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "ADDI"]
theorem dfnAddI (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state) (h : rd ≠ 0) :
    «dfn'ADDI» (rd, (rs1, imm)) s =
      { s with
        c_gpr :=
          holUpdate s.procID
            (holUpdate rd
              (if rs1 = 0 then BitVec.signExtend 64 imm
               else s.c_gpr s.procID rs1 + BitVec.signExtend 64 imm)
              (s.c_gpr s.procID))
            s.c_gpr } := by
  simp only [«dfn'ADDI», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;>
    simp_all [beq_iff_eq, BitVec.zero_add]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "ANDI"]
theorem dfnAndI (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state) (h : rd ≠ 0) :
    «dfn'ANDI» (rd, (rs1, imm)) s =
      { s with
        c_gpr :=
          holUpdate s.procID
            (holUpdate rd
              (if rs1 = 0 then 0
               else s.c_gpr s.procID rs1 &&& BitVec.signExtend 64 imm)
              (s.c_gpr s.procID))
            s.c_gpr } := by
  simp only [«dfn'ANDI», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;>
    simp_all [beq_iff_eq, BitVec.zero_and]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "ORI"]
theorem dfnOrI (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state) (h : rd ≠ 0) :
    «dfn'ORI» (rd, (rs1, imm)) s =
      { s with
        c_gpr :=
          holUpdate s.procID
            (holUpdate rd
              (if rs1 = 0 then BitVec.signExtend 64 imm
               else s.c_gpr s.procID rs1 ||| BitVec.signExtend 64 imm)
              (s.c_gpr s.procID))
            s.c_gpr } := by
  simp only [«dfn'ORI», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;>
    simp_all [beq_iff_eq, BitVec.zero_or]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "XORI"]
theorem dfnXorI (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state) (h : rd ≠ 0) :
    «dfn'XORI» (rd, (rs1, imm)) s =
      { s with
        c_gpr :=
          holUpdate s.procID
            (holUpdate rd
              (if rs1 = 0 then BitVec.signExtend 64 imm
               else s.c_gpr s.procID rs1 ^^^ BitVec.signExtend 64 imm)
              (s.c_gpr s.procID))
            s.c_gpr } := by
  simp only [«dfn'XORI», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;>
    simp_all [beq_iff_eq, BitVec.zero_xor]

end Flapjack.RiscV.L3.Step
