import Flapjack.Compiler.Backend.RiscVConfig.BackendConfig
import Flapjack.Compiler.Backend.RiscVConfig.RegisterNames
import Flapjack.Compiler.Backend.BackendProof.MachineInit
import Flapjack.Compiler.Encoders.RiscV.Target.State
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration

/-!
# `riscv_configProofScript.sml`

The RISC-V machine-configuration predicate and the configuration facts used to
instantiate the generic compiler theorems at RISC-V.
-/

namespace Flapjack.Compiler.Backend.RiscVConfig

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Encoders.RiscV.Target

/-- HOL `is_riscv_machine_config_def` (`riscv_configProofScript.sml:12-19`): the target is
`riscv_target`, the four heap registers are 11/10/13/12 and the callee-saved registers
are `[24; 25; 26]`. -/
@[hol "cakeml/compiler/backend/riscv/proofs/riscv_configProofScript.sml"
  "is_riscv_machine_config_def"]
def isRiscvMachineConfig (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) : Prop :=
  mc.target = riscvTarget ∧
  mc.lenReg = 11 ∧
  mc.ptrReg = 10 ∧
  mc.len2Reg = 13 ∧
  mc.ptr2Reg = 12 ∧
  mc.calleeSavedRegs = [24, 25, 26]

/-- HOL `riscv_init_ok` (`riscv_configProofScript.sml:68-75`):
`is_riscv_machine_config mc ⇒ mc_init_ok riscv_config riscv_backend_config mc`. -/
@[hol "cakeml/compiler/backend/riscv/proofs/riscv_configProofScript.sml" "riscv_init_ok"]
theorem riscvInitOk (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) :
    isRiscvMachineConfig mc → mcInitOk riscvConfig riscvBackendConfig mc := by
  rintro ⟨htarget, hlen, hptr, hlen2, hptr2, hcallee⟩
  have hconfig : riscvTarget.config = riscvConfig := rfl
  have hnames : riscvBackendConfig.stackConf.regNames = riscvNames := rfl
  have hbe : riscvBackendConfig.dataConf.be = false := rfl
  simp only [mcInitOk, htarget, hconfig, hlen, hptr, hlen2, hptr2, hcallee, hnames, hbe,
    StackNames.findNameSpt, riscvNames_lookup_eq]
  decide

end Flapjack.Compiler.Backend.RiscVConfig
