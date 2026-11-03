import Flapjack.Compiler.Backend.X64Config.BackendConfig
import Flapjack.Compiler.Backend.X64Config.BackendProof
import Flapjack.Compiler.Encoders.X64.Machine.Complete
import Flapjack.Compiler.Backend.BackendProof.MachineInit
import Flapjack.Compiler.Backend.LabToTarget.InitializationContracts
import Mathlib.Tactic.IntervalCases

/-!
# x86-64 machine-configuration facts

Counterpart of `cakeml/compiler/backend/x64/proofs/x64_configProofScript.sml`
for the closed x86-64 target.  The encoder-correctness obligation is discharged
by `x64EncoderCorrect` in `Machine/Complete.lean`; `x64EncOk` and `x64TargetOk`
live in `Machine/TargetProof.lean`, and the register-name facts in
`X64Config/BackendProof.lean`.

`is_x64_machine_config` is Flapjack's closed-model instance of CakeML's
predicate.  It is deliberately untagged: HOL's predicate takes
`x64_state`/`x64_proj`, while this one is stated for
`MachineConfig 64 X64State X64Projection`; the carriers are not the same, so it
is not an exact HOL port.  The register numbers are CakeML's
(`len_reg = 6`, `ptr_reg = 7`, `len2_reg = 1`, `ptr2_reg = 2`,
`callee_saved_regs = [12;13;14]`).
-/

namespace Flapjack.Compiler.Backend.X64Config

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.X64 Flapjack.Compiler.Backend.BackendProof

/-- Flapjack's closed-model instance of CakeML's `is_x64_machine_config`
(`x64_configProofScript.sml:8-15`): the target is the closed x86-64 machine and
the register allocation is CakeML's.  Deliberately untagged (see the module
docstring). -/
def isX64MachineConfig (mc : MachineConfig 64 X64State X64Projection) : Prop :=
  mc.target = x64Target ∧
  mc.lenReg = 6 ∧
  mc.ptrReg = 7 ∧
  mc.len2Reg = 1 ∧
  mc.ptr2Reg = 2 ∧
  mc.calleeSavedRegs = [12, 13, 14]

/-- `is_x64_machine_config mc ⇒ mc_conf_ok mc` for the closed target. -/
theorem x64MachineConfigOk (mc : MachineConfig 64 X64State X64Projection)
    (h : isX64MachineConfig mc) :
    LabToTarget.mcConfOk mc := by
  rcases h with ⟨htarget, hlen, hptr, hlen2, hptr2, _⟩
  unfold LabToTarget.mcConfOk
  rw [htarget] at ⊢
  refine ⟨Or.inr rfl, x64EncoderCorrect, ?_, ?_, ?_, ?_, ?_, x64EncOk⟩
  all_goals
    simp only [x64Target_config, hlen, hptr, hlen2, hptr2, x64Config]
    decide

/-- `x64_init_ok` for the closed target and CakeML's x86-64 backend
configuration. -/
theorem x64InitOk (mc : MachineConfig 64 X64State X64Projection) :
    isX64MachineConfig mc → mcInitOk x64Config pancakeX64BackendConfig mc := by
  rintro ⟨htarget, hlen, hptr, hlen2, hptr2, hcallee⟩
  have hnames : pancakeX64BackendConfig.stackConf.regNames = x64Names := rfl
  have hbe : pancakeX64BackendConfig.dataConf.be = false := rfl
  have hfind : StackNames.findNameSpt x64Names = x64NameMap := findNameSpt_x64Names
  simp only [mcInitOk, htarget, x64Target_config, hlen, hptr, hlen2, hptr2, hcallee,
    hnames, hfind, hbe, x64NameMap, x64Config]
  and_intros
  all_goals decide

end Flapjack.Compiler.Backend.X64Config
