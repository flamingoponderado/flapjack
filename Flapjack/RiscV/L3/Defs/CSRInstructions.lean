import Flapjack.RiscV.L3.Defs.CSRDispatch

/-! Complete original CSR register/immediate instruction equations.
Preserves permission selection, zero-source read-only paths, old CSR readback,
full post-write Delta/GPR ordering and illegal-instruction trap branches.
Literal CSRRWI selects Read and skips the CSR write at zimm0, while register
CSRRW always selects Write and writes GPR0=0 at rs1=0. Even rd0 retains the
original CSR read. Source operands are read before the destination GPR update.
These equations are a Run dependency; full Run/Next correctness remains open. -/
namespace Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'CSRRWI_def"]
noncomputable def «dfn'CSRRWI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (zimm, csr)) =>
  (fun (state : riscv_state) => (match (checkCSROp ((csr, ((zimm, ((if ((zimm == (BitVec.ofNat 5 0))) then accessType.Read else accessType.Write)))))) state) with | (v, s) => (if v then ((match (CSR csr s) with | (v_1, s_1) => («write'GPR» (v_1, rd) ((if ((!((zimm == (BitVec.ofNat 5 0))))) then ((writeCSR ((csr, (BitVec.setWidth 64 zimm))) s_1)) else s_1))))) else (signalException ExceptionType.Illegal_Instr s))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'CSRRW_def"]
noncomputable def «dfn'CSRRW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, csr)) =>
  (fun (state : riscv_state) => (match (checkCSROp ((csr, (rs1, accessType.Write))) state) with | (v, s) => (if v then ((match (CSR csr s) with | (v_1, s_1) => («write'GPR» (v_1, rd) ((writeCSR ((csr, (GPR rs1 s_1))) s_1))))) else (signalException ExceptionType.Illegal_Instr s))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'CSRRSI_def"]
noncomputable def «dfn'CSRRSI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (zimm, csr)) =>
  (fun (state : riscv_state) => (match (checkCSROp ((csr, ((zimm, ((if ((zimm == (BitVec.ofNat 5 0))) then accessType.Read else accessType.Write)))))) state) with | (v, s) => (if v then ((match (CSR csr s) with | (v_1, s_1) => («write'GPR» (v_1, rd) ((if ((!((zimm == (BitVec.ofNat 5 0))))) then ((writeCSR ((csr, ((v_1 ||| (BitVec.setWidth 64 zimm))))) s_1)) else s_1))))) else (signalException ExceptionType.Illegal_Instr s))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'CSRRS_def"]
noncomputable def «dfn'CSRRS» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, csr)) =>
  (fun (state : riscv_state) => (match (checkCSROp ((csr, ((rs1, ((if ((rs1 == (BitVec.ofNat 5 0))) then accessType.Read else accessType.Write)))))) state) with | (v, s) => (if v then ((match (CSR csr s) with | (v_1, s_1) => («write'GPR» (v_1, rd) ((if ((!((rs1 == (BitVec.ofNat 5 0))))) then ((writeCSR ((csr, ((v_1 ||| (GPR rs1 s_1))))) s_1)) else s_1))))) else (signalException ExceptionType.Illegal_Instr s))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'CSRRCI_def"]
noncomputable def «dfn'CSRRCI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (zimm, csr)) =>
  (fun (state : riscv_state) => (match (checkCSROp ((csr, ((zimm, ((if ((zimm == (BitVec.ofNat 5 0))) then accessType.Read else accessType.Write)))))) state) with | (v, s) => (if v then ((match (CSR csr s) with | (v_1, s_1) => («write'GPR» (v_1, rd) ((if ((!((zimm == (BitVec.ofNat 5 0))))) then ((writeCSR ((csr, ((v_1 &&& ((~~~(BitVec.setWidth 64 zimm))))))) s_1)) else s_1))))) else (signalException ExceptionType.Illegal_Instr s))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'CSRRC_def"]
noncomputable def «dfn'CSRRC» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, csr)) =>
  (fun (state : riscv_state) => (match (checkCSROp ((csr, ((rs1, ((if ((rs1 == (BitVec.ofNat 5 0))) then accessType.Read else accessType.Write)))))) state) with | (v, s) => (if v then ((match (CSR csr s) with | (v_1, s_1) => («write'GPR» (v_1, rd) ((if ((!((rs1 == (BitVec.ofNat 5 0))))) then ((writeCSR ((csr, ((v_1 &&& ((~~~(GPR rs1 s_1))))))) s_1)) else s_1))))) else (signalException ExceptionType.Illegal_Instr s))))

end Flapjack.RiscV.L3
