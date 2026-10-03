import Flapjack.RiscV.L3.Defs

/-! Full immediate arithmetic/bitwise equations: the original signextends all
word12 immediates to64, including bitwise operations; it does not query mode.
The full source register read precedes the destination update. -/
namespace Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'XORI_def"]
def «dfn'XORI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) ^^^ (BitVec.signExtend 64 imm))), rd)) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ORI_def"]
def «dfn'ORI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) ||| (BitVec.signExtend 64 imm))), rd)) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ANDI_def"]
def «dfn'ANDI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) &&& (BitVec.signExtend 64 imm))), rd)) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ADDI_def"]
def «dfn'ADDI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) + (BitVec.signExtend 64 imm))), rd)) state))

end Flapjack.RiscV.L3
