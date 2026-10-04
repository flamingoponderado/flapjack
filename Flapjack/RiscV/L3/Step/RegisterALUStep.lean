import Flapjack.RiscV.L3.Defs.RegisterALU

/-! Evaluated register-ALU instruction equations (HOL `riscv_step` register group).

The HOL `riscv_stepScript.sml` `class` evaluator normalises each `dfn'X_def`
register clause into an explicit record-update equation.  The destination-write
branch carries the hypothesis `rd <> 0w`; the generated `X_NOP` companion
carries `rd = 0w` and reduces to the unchanged state. Only the destination-write
branch is ported here, with the original hypothesis and the normal form produced by the HOL
evaluator (`applyArithR`/`applyArithI`); the clause inputs are read before the
destination update and a zero source register still reads zero. -/
namespace Flapjack.RiscV.L3.Step

open Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "ADD"]
theorem dfnAdd (rd rs1 rs2 : BitVec 5) (s : riscv_state) (h : rd ≠ 0) :
    «dfn'ADD» (rd, (rs1, rs2)) s =
      { s with
        c_gpr :=
          holUpdate s.procID
            (holUpdate rd
              (if rs1 = 0 then
                (if rs2 = 0 then 0 else s.c_gpr s.procID rs2)
              else if rs2 = 0 then s.c_gpr s.procID rs1
              else s.c_gpr s.procID rs1 + s.c_gpr s.procID rs2)
              (s.c_gpr s.procID))
            s.c_gpr } := by
  simp only [«dfn'ADD», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [beq_iff_eq, BitVec.zero_add, BitVec.add_zero]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SUB"]
theorem dfnSub (rd rs1 rs2 : BitVec 5) (s : riscv_state) (h : rd ≠ 0) :
    «dfn'SUB» (rd, (rs1, rs2)) s =
      { s with
        c_gpr :=
          holUpdate s.procID
            (holUpdate rd
              ((if rs1 = 0 then 0 else s.c_gpr s.procID rs1) -
                (if rs2 = 0 then 0 else s.c_gpr s.procID rs2))
              (s.c_gpr s.procID))
            s.c_gpr } := by
  simp only [«dfn'SUB», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [beq_iff_eq, BitVec.zero_sub, BitVec.sub_zero]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "AND"]
theorem dfnAnd (rd rs1 rs2 : BitVec 5) (s : riscv_state) (h : rd ≠ 0) :
    «dfn'AND» (rd, (rs1, rs2)) s =
      { s with
        c_gpr :=
          holUpdate s.procID
            (holUpdate rd
              (if rs1 = 0 then 0
               else if rs2 = 0 then 0
               else s.c_gpr s.procID rs1 &&& s.c_gpr s.procID rs2)
              (s.c_gpr s.procID))
            s.c_gpr } := by
  simp only [«dfn'AND», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [beq_iff_eq, BitVec.zero_and, BitVec.and_zero]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "OR"]
theorem dfnOr (rd rs1 rs2 : BitVec 5) (s : riscv_state) (h : rd ≠ 0) :
    «dfn'OR» (rd, (rs1, rs2)) s =
      { s with
        c_gpr :=
          holUpdate s.procID
            (holUpdate rd
              (if rs1 = 0 then
                (if rs2 = 0 then 0 else s.c_gpr s.procID rs2)
              else if rs2 = 0 then s.c_gpr s.procID rs1
              else s.c_gpr s.procID rs1 ||| s.c_gpr s.procID rs2)
              (s.c_gpr s.procID))
            s.c_gpr } := by
  simp only [«dfn'OR», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [beq_iff_eq, BitVec.zero_or, BitVec.or_zero]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "XOR"]
theorem dfnXor (rd rs1 rs2 : BitVec 5) (s : riscv_state) (h : rd ≠ 0) :
    «dfn'XOR» (rd, (rs1, rs2)) s =
      { s with
        c_gpr :=
          holUpdate s.procID
            (holUpdate rd
              (if rs1 = 0 then
                (if rs2 = 0 then 0 else s.c_gpr s.procID rs2)
              else if rs2 = 0 then s.c_gpr s.procID rs1
              else s.c_gpr s.procID rs1 ^^^ s.c_gpr s.procID rs2)
              (s.c_gpr s.procID))
            s.c_gpr } := by
  simp only [«dfn'XOR», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [beq_iff_eq, BitVec.zero_xor, BitVec.xor_zero]

end Flapjack.RiscV.L3.Step
