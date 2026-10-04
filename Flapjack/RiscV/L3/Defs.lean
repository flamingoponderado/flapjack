import Flapjack.RiscV.L3.Support

/-! Integer state operations retained on the riscv-mi branch. -/
namespace Flapjack.RiscV.L3

/-- HOL `riscv$MCSR` (`MCSR_def`), mechanically rendered from the elaborated HOL definition. -/
def MCSR (state : riscv_state) : MachineCSR :=
  (state.c_MCSR state.procID)

/-- HOL `riscv$write'NextFetch` (`write'NextFetch_def`), mechanically rendered from the elaborated HOL definition. -/
def «write'NextFetch» (value : (Option TransferControl)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_NextFetch := ((fun (_eta1 : ((BitVec 8) → (Option TransferControl))) => (holUpdate state.procID value state.c_NextFetch))) r.c_NextFetch }))

/-- HOL `riscv$setTrap` (`setTrap_def`), mechanically rendered from the elaborated HOL definition. -/
noncomputable def setTrap (arg0 : (ExceptionType × (Option (BitVec 64)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (e, badaddr) =>
  (fun (state : riscv_state) => («write'NextFetch» ((some ((TransferControl.Trap ((let r := ((let r := (Flapjack.holArb SynchronousTrap); { r with trap := ((fun (_eta1 : ExceptionType) => e)) r.trap })); { r with badaddr := ((fun (_eta1 : (Option (BitVec 64))) => badaddr)) r.badaddr })))))) state))

/-- HOL `riscv$signalException` (`signalException_def`), mechanically rendered from the elaborated HOL definition. -/
noncomputable def signalException (e : ExceptionType) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (setTrap ((e, ((none : (Option (BitVec 64)))))) state))

/-- HOL `riscv$gpr` (`gpr_def`), mechanically rendered from the elaborated HOL definition. -/
def gpr (n : (BitVec 5)) : (riscv_state → (BitVec 64)) :=
  (fun (state : riscv_state) => (state.c_gpr state.procID n))

/-- HOL `riscv$GPR` (`GPR_def`), mechanically rendered from the elaborated HOL definition. -/
def GPR (n : (BitVec 5)) : (riscv_state → (BitVec 64)) :=
  (fun (state : riscv_state) => (if ((n == (BitVec.ofNat 5 0))) then (BitVec.ofNat 64 0) else (gpr n state)))

/-- HOL `riscv$Delta` (`Delta_def`), mechanically rendered from the elaborated HOL definition. -/
def Delta (state : riscv_state) : StateDelta :=
  (state.c_update state.procID)

/-- HOL `riscv$write'Delta` (`write'Delta_def`), mechanically rendered from the elaborated HOL definition. -/
def «write'Delta» (value : StateDelta) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_update := ((fun (_eta1 : ((BitVec 8) → StateDelta)) => (holUpdate state.procID value state.c_update))) r.c_update }))

/-- HOL `riscv$write'gpr` (`write'gpr_def`), mechanically rendered from the elaborated HOL definition. -/
def «write'gpr» (arg0 : ((BitVec 64) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (value, n) =>
  (fun (state : riscv_state) => (let r := state; { r with c_gpr := ((fun (_eta1 : ((BitVec 8) → ((BitVec 5) → (BitVec 64)))) => ((holUpdate state.procID ((holUpdate n value (state.c_gpr state.procID))) state.c_gpr)))) r.c_gpr }))

/-- HOL `riscv$write'GPR` (`write'GPR_def`), mechanically rendered from the elaborated HOL definition. -/
def «write'GPR» (arg0 : ((BitVec 64) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (value, n) =>
  (fun (state : riscv_state) => (if ((!((n == (BitVec.ofNat 5 0))))) then ((«write'gpr» (value, n) state)) else state))

/-- HOL `riscv$NextFetch` (`NextFetch_def`), mechanically rendered from the elaborated HOL definition. -/
def NextFetch (state : riscv_state) : (Option TransferControl) :=
  (state.c_NextFetch state.procID)

/-- HOL `riscv$ext_status` (`ext_status_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "ext_status_def"]
def ext_status (e : ExtStatus) : (BitVec 2) :=
  (match e with | .Off => (BitVec.ofNat 2 0) | .Initial => (BitVec.ofNat 2 1) | .Clean => (BitVec.ofNat 2 2) | .Dirty => (BitVec.ofNat 2 3))

end Flapjack.RiscV.L3
