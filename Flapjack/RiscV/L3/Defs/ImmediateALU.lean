import Flapjack.RiscV.L3.Defs

/-! Full immediate arithmetic/bitwise equations: the original signextends all
word12 immediates to64, including bitwise operations; it does not query mode.
The full source register read precedes the destination update. -/
namespace Flapjack.RiscV.L3

def «dfn'XORI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) ^^^ (BitVec.signExtend 64 imm))), rd)) state))

def «dfn'ORI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) ||| (BitVec.signExtend 64 imm))), rd)) state))

def «dfn'ANDI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) &&& (BitVec.signExtend 64 imm))), rd)) state))

def «dfn'ADDI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) + (BitVec.signExtend 64 imm))), rd)) state))

end Flapjack.RiscV.L3
