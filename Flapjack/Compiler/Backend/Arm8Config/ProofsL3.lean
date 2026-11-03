import Flapjack.Compiler.Backend.Arm8Config.BackendConfig
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Complete
import Flapjack.Compiler.Backend.BackendProof.MachineInit
import Flapjack.Compiler.Backend.LabToTarget.InitializationContracts
import Mathlib.Tactic.IntervalCases

/-!
# ARMv8 machine-configuration facts over the L3 carriers

Counterpart of `cakeml/compiler/backend/arm8/proofs/arm8_configProofScript.sml`
at the L3 ARMv8 target: `is_arm8_machine_config` and
`is_arm8_machine_config mc ⇒ mc_conf_ok mc` over HOL's `arm8_state`/`arm8_proj`
carriers.  The encoder-correctness obligation is discharged by
`arm8EncoderCorrectL3` in `L3/CorrectnessEncoding/Complete.lean`.

This file is a near-duplicate of `Arm8Config.Proofs` for the closed model: the
two differ only in the target record, the configuration and the
`arm8_state`/`Arm8State` carriers.  Keep the two proofs in step.
-/

namespace Flapjack.Compiler.Backend.Arm8Config

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3
open Flapjack.Compiler.Encoders.Arm8.L3.Target
open Flapjack.Compiler.Backend.BackendProof

/-- CakeML's `is_arm8_machine_config` (`arm8_configProofScript.sml`) over the L3
`arm8_state` carrier and the L3 `arm8_proj` projection.  The register roles,
callee-saved set and target are HOL's; only the state/projection carriers are
the L3 ones. -/
def isArm8MachineConfigL3
    (mc : MachineConfig 64 arm8_state Arm8L3Projection) : Prop :=
  mc.target = arm8TargetL3 ∧
  mc.lenReg = 1 ∧
  mc.ptrReg = 0 ∧
  mc.len2Reg = 3 ∧
  mc.ptr2Reg = 2 ∧
  mc.calleeSavedRegs = [19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

/-- `is_arm8_machine_config mc ⇒ mc_conf_ok mc` at the L3 ARMv8 target: the
encoder-correctness component is `arm8EncoderCorrectL3`, the encoding
invariant `arm8ConfigL3_encOk`, and the register guards are decided. -/
theorem arm8MachineConfigOkL3
    (mc : MachineConfig 64 arm8_state Arm8L3Projection)
    (h : isArm8MachineConfigL3 mc) :
    LabToTarget.mcConfOk mc := by
  rcases h with ⟨htarget, hlen, hptr, hlen2, hptr2, _⟩
  unfold LabToTarget.mcConfOk
  rw [htarget] at ⊢
  refine ⟨Or.inr rfl, arm8EncoderCorrectL3, ?_, ?_, ?_, ?_, ?_, arm8ConfigL3_encOk⟩
  all_goals
    simp only [arm8TargetL3_config, hlen, hptr, hlen2, hptr2, arm8ConfigL3]
    decide

/-- `arm8_init_ok` at the L3 ARMv8 target and CakeML's ARMv8 backend
configuration. -/
theorem arm8InitOkL3 (mc : MachineConfig 64 arm8_state Arm8L3Projection) :
    isArm8MachineConfigL3 mc →
      mcInitOk arm8ConfigL3 pancakeArm8BackendConfig mc := by
  rintro ⟨htarget, hlen, hptr, hlen2, hptr2, hcallee⟩
  have hnames : pancakeArm8BackendConfig.stackConf.regNames = arm8Names := rfl
  have hbe : pancakeArm8BackendConfig.dataConf.be = false := rfl
  have hfind : StackNames.findNameSpt arm8Names = arm8NameMap :=
    funext arm8Names_lookup_eq
  simp only [mcInitOk, htarget, arm8TargetL3_config, hlen, hptr, hlen2, hptr2, hcallee,
    hnames, hfind, hbe, arm8NameMap, arm8ConfigL3]
  and_intros
  all_goals decide

end Flapjack.Compiler.Backend.Arm8Config
