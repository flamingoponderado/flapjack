import Flapjack.RiscV.L3.Defs

/-! Complete raw-bit sign injection and register moves. These instructions
preserve sign/payload fields through literal FPRS/FPRD helpers, without
real arithmetic or rounding. FPR register zero is writable; GPR zero is not. -/
namespace Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSGNJ_S_def"]
def «dfn'FSGNJ_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (writeFPRS ((rd, ((BitVec.setWidth 32 (((holV2w 1 ((((FP32_Sign (FPRS rs2 state))) :: (([] : (List Bool))))))) ++ ((holWordExtract 31 30 0 (FPRS rs1 state)))))))) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSGNJ_D_def"]
def «dfn'FSGNJ_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (writeFPRD ((rd, ((BitVec.setWidth 64 (((holV2w 1 ((((FP64_Sign (FPRD rs2 state))) :: (([] : (List Bool))))))) ++ ((holWordExtract 63 62 0 (FPRD rs1 state)))))))) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSGNJX_S_def"]
def «dfn'FSGNJX_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 32) := (FPRS rs1 state); (writeFPRS ((rd, ((BitVec.setWidth 32 (((((holV2w 1 ((((FP32_Sign (FPRS rs2 state))) :: (([] : (List Bool))))))) ^^^ ((holV2w 1 (((FP32_Sign v) :: (([] : (List Bool))))))))) ++ (holWordExtract 31 30 0 v)))))) state)))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSGNJX_D_def"]
def «dfn'FSGNJX_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (FPRD rs1 state); (writeFPRD ((rd, ((BitVec.setWidth 64 (((((holV2w 1 ((((FP64_Sign (FPRD rs2 state))) :: (([] : (List Bool))))))) ^^^ ((holV2w 1 (((FP64_Sign v) :: (([] : (List Bool))))))))) ++ (holWordExtract 63 62 0 v)))))) state)))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSGNJN_S_def"]
def «dfn'FSGNJN_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (writeFPRS ((rd, ((BitVec.setWidth 32 (((holV2w 1 ((((!((FP32_Sign (FPRS rs2 state))))) :: (([] : (List Bool))))))) ++ ((holWordExtract 31 30 0 (FPRS rs1 state)))))))) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSGNJN_D_def"]
def «dfn'FSGNJN_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (writeFPRD ((rd, ((BitVec.setWidth 64 (((holV2w 1 ((((!((FP64_Sign (FPRD rs2 state))))) :: (([] : (List Bool))))))) ++ ((holWordExtract 63 62 0 (FPRD rs1 state)))))))) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMV_X_S_def"]
def «dfn'FMV_X_S» (arg0 : ((BitVec 5) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, rs) =>
  (fun (state : riscv_state) => («write'GPR» ((((BitVec.signExtend 64 (FPRS rs state))), rd)) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMV_X_D_def"]
def «dfn'FMV_X_D» (arg0 : ((BitVec 5) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, rs) =>
  (fun (state : riscv_state) => («write'GPR» ((((BitVec.signExtend 64 (FPRD rs state))), rd)) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMV_S_X_def"]
def «dfn'FMV_S_X» (arg0 : ((BitVec 5) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, rs) =>
  (fun (state : riscv_state) => (writeFPRS ((rd, ((holWordExtract 32 31 0 (GPR rs state))))) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMV_D_X_def"]
def «dfn'FMV_D_X» (arg0 : ((BitVec 5) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, rs) =>
  (fun (state : riscv_state) => (writeFPRD ((rd, (GPR rs state))) state))

end Flapjack.RiscV.L3
