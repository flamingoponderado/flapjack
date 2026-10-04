import Flapjack.Compiler.Backend.RiscVConfig.BackendConfig
import Flapjack.Compiler.Backend.RiscVConfig.RegisterNames
import Flapjack.Compiler.Backend.BackendProof.MachineInit
import Flapjack.Compiler.Backend.BackendProof.ConfigOk
import Flapjack.Compiler.Encoders.RiscV.Target.State
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import Flapjack.Compiler.Backend.LabToTarget.InitializationContracts
import Flapjack.RiscV.CorrectnessEncoding.Complete

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

/-- HOL `riscv_machine_config_ok` (`riscv_configProofScript.sml:54-66`):
`is_riscv_machine_config mc ⇒ mc_conf_ok mc`. `encoder_correct` is the assembled
`riscv_encoder_correct`, `enc_ok` comes from `riscv_target_ok`, and the remaining
conjuncts (`good_dimindex (:64)` and `reg_ok` of the four heap registers and the
link register) are decided on the concrete configuration. -/
@[hol "cakeml/compiler/backend/riscv/proofs/riscv_configProofScript.sml"
  "riscv_machine_config_ok"]
theorem riscvMachineConfigOk (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) :
    isRiscvMachineConfig mc → LabToTarget.mcConfOk mc := by
  rintro ⟨htarget, hlen, hptr, hlen2, hptr2, -⟩
  refine ⟨.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htarget]; exact RiscV.TargetProof.riscv_encoder_correct
  all_goals first
    | (rw [htarget]; exact RiscV.TargetProof.riscv_target_ok.1)
    | (simp only [htarget, hlen, hptr, hlen2, hptr2]; decide)

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

/-- HOL `riscv_backend_config_ok` (`riscv_configProofScript.sml:27-52`):
`backend_config_ok riscv_config riscv_backend_config`. -/
@[hol "cakeml/compiler/backend/riscv/proofs/riscv_configProofScript.sml"
  "riscv_backend_config_ok"]
theorem riscvBackendConfigOk : backendConfigOk riscvConfig riscvBackendConfig := by
  unfold backendConfigOk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | rfl | skip
  case refine_2 => show 0 < 10; decide
  case refine_4 => decide
  case refine_7 =>
    simp only [DataToWord.confOk, DataToWord.shiftLength, riscvBackendConfig,
      Flapjack.wordShiftAmount]
    decide
  case refine_8 => simp [riscvBackendConfig]
  case refine_9 => simp [riscvBackendConfig, riscvConfig]
  case refine_10 => simp [riscvBackendConfig, riscvConfig]
  case refine_11 => simp [riscvBackendConfig, riscvConfig]
  case refine_12 =>
    simp only [StackRemove.maxStackAlloc, DataToWord.maxHeapLimit, DataToWord.shiftLength,
      riscvBackendConfig, Flapjack.wordShiftAmount]
    decide
  case refine_21 => simp [riscvBackendConfig]
  case refine_24 => simp [StackProps.fixedNames, riscvConfig]
  case refine_16 =>
    intro w ⟨h1, h2⟩
    rw [BitVec.sle_iff_toInt_le] at h1 h2
    have m8 : (-8 : BitVec 64).toInt = -8 := by decide
    have p8 : (8 : BitVec 64).toInt = 8 := by decide
    have lo : (-2048 : BitVec 64).toInt = -2048 := by decide
    have hi : (2047 : BitVec 64).toInt = 2047 := by decide
    simp only [asmByteOffsetOkExact, asmOffsetOkExact, riscvConfig, asmAligned, lo, hi, m8, p8,
      Nat.pow_zero, Nat.mod_one, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
    exact ⟨⟨by omega, by omega⟩, trivial⟩
  case refine_22 =>
    have hfun : StackNames.findNameSpt riscvBackendConfig.stackConf.regNames =
        Flapjack.RiscV.riscvRegisterName := funext fun r => riscvNames_lookup_eq r
    rw [hfun]
    constructor
    · intro a b h
      by_cases ha : a < 32 <;> by_cases hb : b < 32
      · exact Flapjack.RiscV.riscvRegisterName_injective_lt_32 ha hb h
      · have := Flapjack.RiscV.riscvRegisterName_lt_32 ha
        rw [h, Flapjack.RiscV.riscvRegisterName_id_of_ge_32 (by omega)] at this
        omega
      · have := Flapjack.RiscV.riscvRegisterName_lt_32 hb
        rw [← h, Flapjack.RiscV.riscvRegisterName_id_of_ge_32 (by omega)] at this
        omega
      · rwa [Flapjack.RiscV.riscvRegisterName_id_of_ge_32 (by omega),
          Flapjack.RiscV.riscvRegisterName_id_of_ge_32 (by omega)] at h
    · intro t
      by_cases ht : t < 32
      · obtain ⟨n, -, hn⟩ := Flapjack.RiscV.riscvRegisterName_surjective_lt_32 ht
        exact ⟨n, hn⟩
      · exact ⟨t, Flapjack.RiscV.riscvRegisterName_id_of_ge_32 (by omega)⟩
  case refine_23 =>
    have hnames : riscvBackendConfig.stackConf.regNames = riscvNames := rfl
    have hf : StackNames.findName (fun key => Flapjack.sptLookup key riscvNames) =
        Flapjack.RiscV.riscvRegisterName := by
      funext r
      rw [← riscvNames_lookup_eq]
      simp only [StackNames.findName, FLOOKUP]
      cases Flapjack.sptLookup r riscvNames <;> rfl
    simp only [StackNames.namesOkSptHOL, hnames, hf]
    decide
  case refine_25 =>
    intro s
    cases s
    all_goals first | decide | skip
    rename_i w
    revert w
    decide
  case refine_26 =>
    intro s
    cases s
    all_goals first | decide | skip
    rename_i w
    revert w
    decide
  case refine_27 =>
    intro n hn
    simp only [StackRemove.maxStackAlloc] at hn
    have hv : (BitVec.ofNat 64 (n * (64 / 8))).toInt = n * 8 := by
      rw [BitVec.toInt_eq_toNat_of_lt]
      · simp; omega
      · simp; omega
    have lo : (-2048 : BitVec 64).toInt = -2048 := by decide
    have hi : (2047 : BitVec 64).toInt = 2047 := by decide
    simp only [riscvConfig, BitVec.slt_iff_toInt_lt, BitVec.sle_iff_toInt_le, hv, lo, hi,
      Bool.and_eq_true]
    omega

end Flapjack.Compiler.Backend.RiscVConfig
