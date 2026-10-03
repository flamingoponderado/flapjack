import Flapjack.RiscV.L3.Defs

/-! Full literal register arithmetic and bitwise equations. These original clauses
use word64 operands irrespective of architecture; no mode check is added.
Source reads precede destination update and register zero stays suppressed. -/
namespace Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'XOR_def"]
def «dfn'XOR» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) ^^^ (GPR rs2 state))), rd)) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SUB_def"]
def «dfn'SUB» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) - (GPR rs2 state))), rd)) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'OR_def"]
def «dfn'OR» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) ||| (GPR rs2 state))), rd)) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AND_def"]
def «dfn'AND» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) &&& (GPR rs2 state))), rd)) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ADD_def"]
def «dfn'ADD» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) + (GPR rs2 state))), rd)) state))

end Flapjack.RiscV.L3
