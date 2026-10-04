import Flapjack.RiscV.L3.Defs.AddressException

import Flapjack.RiscV.L3.Defs.Fetch


/-! Complete upper-immediate and jump equations. Original JAL checks target bit0,
not a stricter alignment rule; JALR masks with signextended word2 value2.
Link uses original PC plus current Skip, and source reads precede rd updates.
Full Run/Next correctness remains open. -/
namespace Flapjack.RiscV.L3


def Skip (state : riscv_state) : (BitVec 64) :=
  (state.c_Skip state.procID)

def branchTo (newPC : (BitVec 64)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => («write'NextFetch» ((some (TransferControl.BranchTo newPC))) state))

noncomputable def «dfn'JALR» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((((GPR rs1 state) + (BitVec.signExtend 64 imm))) &&& ((BitVec.signExtend 64 (BitVec.ofNat 2 2)))); (if (v.getLsbD 0) then ((signalAddressException (ExceptionType.Fetch_Misaligned, v) state)) else ((branchTo v ((«write'GPR» (((((PC state) + (Skip state))), rd)) state)))))))

noncomputable def «dfn'JAL» (arg0 : ((BitVec 5) × (BitVec 20))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, imm) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((PC state) + (((BitVec.signExtend 64 imm) <<< 1))); (if (v.getLsbD 0) then ((signalAddressException (ExceptionType.Fetch_Misaligned, v) state)) else ((branchTo v ((«write'GPR» (((((PC state) + (Skip state))), rd)) state)))))))

def «dfn'LUI» (arg0 : ((BitVec 5) × (BitVec 20))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, imm) =>
  (fun (state : riscv_state) => («write'GPR» ((((BitVec.signExtend 64 ((BitVec.setWidth 32 (imm ++ (BitVec.ofNat 12 0)))))), rd)) state))

def «dfn'AUIPC» (arg0 : ((BitVec 5) × (BitVec 20))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, imm) =>
  (fun (state : riscv_state) => («write'GPR» (((((PC state) + ((BitVec.signExtend 64 ((BitVec.setWidth 32 (imm ++ (BitVec.ofNat 12 0)))))))), rd)) state))


end Flapjack.RiscV.L3
