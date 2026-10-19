import Flapjack.Compiler.Backend.Arm8Config.BackendConfig
import Flapjack.Compiler.Encoders.Arm8.Machine.Complete
import Flapjack.Compiler.Backend.BackendProof.MachineInit
import Flapjack.Compiler.Backend.LabToTarget.InitializationContracts
import Mathlib.Tactic.IntervalCases

/-!
# ARMv8 machine-configuration facts

Counterpart of `cakeml/compiler/backend/arm8/proofs/arm8_configProofScript.sml`
for the closed ARMv8 target.  The encoder-correctness obligation is discharged
by `arm8EncoderCorrect` in `Machine/Complete.lean`.
-/

namespace Flapjack.Compiler.Backend.Arm8Config

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.Arm8
open Flapjack.Compiler.Backend.BackendProof

/-- Flapjack's closed-model instance of CakeML's `is_arm8_machine_config`.
Deliberately untagged: HOL's predicate takes `arm8_state`/`arm8_proj`, while
this one is stated for `MachineConfig 64 Arm8State Arm8Projection`; the carriers
are not the same, so it is not an exact HOL port. -/
def isArm8MachineConfig
    (mc : MachineConfig 64 Arm8State Arm8Projection) : Prop :=
  mc.target = arm8Target ∧
  mc.lenReg = 1 ∧
  mc.ptrReg = 0 ∧
  mc.len2Reg = 3 ∧
  mc.ptr2Reg = 2 ∧
  mc.calleeSavedRegs = [19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

/-- `is_arm8_machine_config mc ⇒ mc_conf_ok mc` for the closed target. -/
theorem arm8MachineConfigOk
    (mc : MachineConfig 64 Arm8State Arm8Projection)
    (h : isArm8MachineConfig mc) :
    LabToTarget.mcConfOk mc := by
  rcases h with ⟨htarget, hlen, hptr, hlen2, hptr2, _⟩
  unfold LabToTarget.mcConfOk
  rw [htarget] at ⊢
  refine ⟨Or.inr rfl, arm8EncoderCorrect, ?_, ?_, ?_, ?_, ?_, arm8EncOk⟩
  all_goals
    simp only [arm8Target_config, hlen, hptr, hlen2, hptr2, arm8Config]
    decide

/-- `arm8_init_ok` for the closed target and CakeML's ARMv8 backend
configuration. -/
theorem arm8InitOk (mc : MachineConfig 64 Arm8State Arm8Projection) :
    isArm8MachineConfig mc →
      mcInitOk arm8Config pancakeArm8BackendConfig mc := by
  rintro ⟨htarget, hlen, hptr, hlen2, hptr2, hcallee⟩
  have hnames : pancakeArm8BackendConfig.stackConf.regNames = arm8Names := rfl
  have hbe : pancakeArm8BackendConfig.dataConf.be = false := rfl
  have hfind : StackNames.findNameSpt arm8Names = arm8NameMap :=
    funext arm8Names_lookup_eq
  simp only [mcInitOk, htarget, arm8Target_config, hlen, hptr, hlen2, hptr2, hcallee,
    hnames, hfind, hbe, arm8NameMap, arm8Config]
  and_intros
  all_goals decide

end Flapjack.Compiler.Backend.Arm8Config
