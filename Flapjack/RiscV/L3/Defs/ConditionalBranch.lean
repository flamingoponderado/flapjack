import Flapjack.RiscV.L3.Defs.UpperJump

import Flapjack.RiscV.L3.Defs.IntegerLoadMode


/-! Complete literal six conditional branch equations, source6879-7083.
Both in32BitMode calls and their returned states are retained. Selector0
compares signextended low32 values; selectors2/3 compare full64; unspecified
selector1 retains the original architecture ARB and first-exception behavior.
Taken paths call branchTo directly, including odd targets. They do not perform
JAL-style alignment checks or update GPR/PC/Delta. Full Run/Next remains open. -/
namespace Flapjack.RiscV.L3


@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'BNE_def"]
noncomputable def «dfn'BNE» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (if ((!((((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) == ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0))))))) then ((branchTo (((PC s0) + (((BitVec.signExtend 64 offs) <<< 1)))) s0)) else s0))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'BLTU_def"]
noncomputable def «dfn'BLTU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (if ((BitVec.ult ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0))))) then ((branchTo (((PC s0) + (((BitVec.signExtend 64 offs) <<< 1)))) s0)) else s0))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'BLT_def"]
noncomputable def «dfn'BLT» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (if ((BitVec.slt ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0))))) then ((branchTo (((PC s0) + (((BitVec.signExtend 64 offs) <<< 1)))) s0)) else s0))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'BGEU_def"]
noncomputable def «dfn'BGEU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (if ((!(BitVec.ult ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0)))))) then ((branchTo (((PC s0) + (((BitVec.signExtend 64 offs) <<< 1)))) s0)) else s0))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'BGE_def"]
noncomputable def «dfn'BGE» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (if ((BitVec.sle ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0))) ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))))) then ((branchTo (((PC s0) + (((BitVec.signExtend 64 offs) <<< 1)))) s0)) else s0))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'BEQ_def"]
noncomputable def «dfn'BEQ» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (if ((((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) == ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0))))) then ((branchTo (((PC s0) + (((BitVec.signExtend 64 offs) <<< 1)))) s0)) else s0))))


end Flapjack.RiscV.L3
