import Flapjack.RiscV.L3.Defs
import Flapjack.RiscV.L3.Defs.CSRAccess
import Flapjack.RiscV.L3.Defs.MMU.Primitives
import Flapjack.RiscV.L3.Defs.AddressException

/-! Complete native supervisor transfer and instruction-fetch exception equations.
The transfer copies machine cause, bad address and exception PC in source order,
then sets MPRV to Supervisor and NextFetch to Mrts. No mode or success premise. -/
namespace Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'SCSR_def"]
def «write'SCSR» (value : SupervisorCSR) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_SCSR := ((fun (_eta1 : ((BitVec 8) → SupervisorCSR)) => (holUpdate state.procID value state.c_SCSR))) r.c_SCSR }))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'MRTS_def"]
def «dfn'MRTS» (state : riscv_state) : riscv_state :=
  (match (let s0 : riscv_state := («write'SCSR» ((let r := (SCSR state); { r with scause := ((fun (_eta1 : mcause) => ((MCSR state).mcause))) r.scause })) state); ((SCSR s0), s0)) with | (v, s) => (match (let s0 : riscv_state := («write'SCSR» ((let r := v; { r with sbadaddr := ((fun (_eta1 : (BitVec 64)) => ((MCSR s).mbadaddr))) r.sbadaddr })) s); ((SCSR s0), s0)) with | (v_1, s_1) => (match (let s0 : riscv_state := («write'SCSR» ((let r := v_1; { r with sepc := ((fun (_eta1 : (BitVec 64)) => ((MCSR s_1).mepc))) r.sepc })) s_1); ((MCSR s0), s0)) with | (v, s) => («write'NextFetch» (some TransferControl.Mrts) ((«write'MCSR» ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MPRV := ((fun (_eta1 : (BitVec 2)) => (privLevel Privilege.Supervisor))) r.MPRV })))) r.mstatus })) s))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FETCH_MISALIGNED_def"]
noncomputable def «dfn'FETCH_MISALIGNED» (addr : (BitVec 64)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (signalAddressException (ExceptionType.Fetch_Misaligned, addr) state))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FETCH_FAULT_def"]
noncomputable def «dfn'FETCH_FAULT» (addr : (BitVec 64)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (signalAddressException (ExceptionType.Fetch_Fault, addr) state))

end Flapjack.RiscV.L3
