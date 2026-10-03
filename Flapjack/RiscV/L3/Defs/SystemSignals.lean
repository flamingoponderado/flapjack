import Flapjack.RiscV.L3.Defs
import Flapjack.RiscV.L3.Defs.MMU.Primitives
namespace Flapjack.RiscV.L3

/-- Literal original complete native control/exception equation. Environment
calls retain the original MCSR.mstatus.MPRV selector through privilege, while
breakpoint/illegal instructions use original signalException and ERET writes
Ereturn directly. No architecture, privilege-success or core-bound premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'UnknownInstruction_def"]
noncomputable def «dfn'UnknownInstruction» (state : riscv_state) : riscv_state :=
  (signalException ExceptionType.Illegal_Instr state)

/-- Literal original complete native control/exception equation. Environment
calls retain the original MCSR.mstatus.MPRV selector through privilege, while
breakpoint/illegal instructions use original signalException and ERET writes
Ereturn directly. No architecture, privilege-success or core-bound premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ERET_def"]
noncomputable def «dfn'ERET» (state : riscv_state) : riscv_state :=
  («write'NextFetch» (some TransferControl.Ereturn) state)

/-- Literal original complete native control/exception equation. Environment
calls retain the original MCSR.mstatus.MPRV selector through privilege, while
breakpoint/illegal instructions use original signalException and ERET writes
Ereturn directly. No architecture, privilege-success or core-bound premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "signalEnvCall_def"]
noncomputable def signalEnvCall (_u_ : Unit) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (signalException ((match (privilege (((MCSR state).mstatus).MPRV)) with | .User => ExceptionType.UMode_Env_Call | .Supervisor => ExceptionType.SMode_Env_Call | .Hypervisor => ExceptionType.HMode_Env_Call | .Machine => ExceptionType.MMode_Env_Call)) state))

/-- Literal original complete native control/exception equation. Environment
calls retain the original MCSR.mstatus.MPRV selector through privilege, while
breakpoint/illegal instructions use original signalException and ERET writes
Ereturn directly. No architecture, privilege-success or core-bound premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ECALL_def"]
noncomputable def «dfn'ECALL» (state : riscv_state) : riscv_state :=
  (signalEnvCall () state)

/-- Literal original complete native control/exception equation. Environment
calls retain the original MCSR.mstatus.MPRV selector through privilege, while
breakpoint/illegal instructions use original signalException and ERET writes
Ereturn directly. No architecture, privilege-success or core-bound premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'EBREAK_def"]
noncomputable def «dfn'EBREAK» (state : riscv_state) : riscv_state :=
  (signalException ExceptionType.Breakpoint state)


/-- Flapjack-only unconditional whole-state normal form; no separate HOL original. -/
theorem unknownInstructionWholeState (s : riscv_state) : «dfn'UnknownInstruction» s = signalException .Illegal_Instr s := by
  rfl

/-- Flapjack-only unconditional whole-state normal form; no separate HOL original. -/
theorem eretWholeState (s : riscv_state) : «dfn'ERET» s = «write'NextFetch» (some .Ereturn) s := by
  rfl

/-- Flapjack-only unconditional whole-state normal form; no separate HOL original. -/
theorem ebreakWholeState (s : riscv_state) : «dfn'EBREAK» s = signalException .Breakpoint s := by
  rfl

/-- Flapjack-only unconditional whole-state normal form; no separate HOL original. -/
theorem ecallWholeState (s : riscv_state) : «dfn'ECALL» s = signalEnvCall () s := by
  rfl

/-- Flapjack-only unconditional complete privilege-selector normal form. -/
theorem signalEnvCallWholeState (s : riscv_state) :
    signalEnvCall () s = signalException
      (match privilege (MCSR s).mstatus.MPRV with
       | .User => .UMode_Env_Call | .Supervisor => .SMode_Env_Call
       | .Hypervisor => .HMode_Env_Call | .Machine => .MMode_Env_Call) s := by
  rfl

end Flapjack.RiscV.L3
