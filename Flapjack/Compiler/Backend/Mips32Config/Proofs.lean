import Flapjack.Compiler.Backend.Mips32Config.BackendConfig
import Flapjack.Compiler.Backend.BackendProof.MachineInit
import Flapjack.Compiler.Backend.BackendProof.ConfigOk
import Flapjack.Compiler.Backend.LabToTarget.InitializationContracts
import Flapjack.Mips32.TargetProof.Complete
import Mathlib.Tactic.IntervalCases

/-!
# MIPS32 (Ziren) machine and backend configuration facts

The counterparts, for the MIPS32 target, of CakeML's `mips_configProofScript.sml`: the
machine-configuration predicate (CakeML's MIPS heap registers `$a0`-`$a3` and callee-saved
`$s5`-`$s7`), `mc_conf_ok` from `mips32_encoder_correct`, `mc_init_ok` and
`backend_config_ok`. Flapjack-specific (no MIPS32 in CakeML), so untagged.
-/

namespace Flapjack.Compiler.Backend.Mips32Config

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Encoders.Mips32

/-- The MIPS32 machine configurations: the target is `mips32Target`, the four heap registers
are `$a1`/`$a0`/`$a3`/`$a2` (5/4/7/6) and the callee-saved registers are `[21; 22; 23]`,
as in CakeML's `is_mips_machine_config`. -/
def isMips32MachineConfig
    (mc : MachineConfig 32 ZirenDet.Isa.State Mips32Projection) : Prop :=
  mc.target = mips32Target ∧
  mc.lenReg = 5 ∧
  mc.ptrReg = 4 ∧
  mc.len2Reg = 7 ∧
  mc.ptr2Reg = 6 ∧
  mc.calleeSavedRegs = [21, 22, 23]

/-- `is_mips32_machine_config mc ⇒ mc_conf_ok mc`, from `mips32_encoder_correct`. -/
theorem mips32MachineConfigOk (mc : MachineConfig 32 ZirenDet.Isa.State Mips32Projection) :
    isMips32MachineConfig mc → LabToTarget.mcConfOk mc := by
  rintro ⟨htarget, hlen, hptr, hlen2, hptr2, -⟩
  have henc := Flapjack.Mips32.TargetProof.mips32_encoder_correct
  rw [← htarget] at henc
  refine ⟨Or.inl rfl, henc, ?_, ?_, ?_, ?_, ?_, henc.1.1⟩
  all_goals simp only [htarget, hlen, hptr, hlen2, hptr2]; decide

/-- `is_mips32_machine_config mc ⇒ mc_init_ok mips32_config mips32_backend_config mc`. -/
theorem mips32InitOk (mc : MachineConfig 32 ZirenDet.Isa.State Mips32Projection) :
    isMips32MachineConfig mc → mcInitOk mips32Config mips32BackendConfig mc := by
  rintro ⟨htarget, hlen, hptr, hlen2, hptr2, hcallee⟩
  have hconfig : mips32Target.config = mips32Config := rfl
  have hnames : mips32BackendConfig.stackConf.regNames = mipsNames := rfl
  have hbe : mips32BackendConfig.dataConf.be = false := rfl
  simp only [mcInitOk, htarget, hconfig, hlen, hptr, hlen2, hptr2, hcallee, hnames, hbe,
    StackNames.findNameSpt, mipsNames_lookup_eq]
  and_intros
  all_goals first | rfl | decide

end Flapjack.Compiler.Backend.Mips32Config

namespace Flapjack.Compiler.Backend.Mips32Config
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Encoders.Mips32

/-- The inverse of `mipsNameMap` (Flapjack infrastructure). -/
def mipsNameInv (register : Nat) : Nat :=
  match register with
  | 31 => 0 | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 4 | 24 => 5 | 3 => 6 | 2 => 7 | 0 => 24
  | 1 => 31 | r => r

theorem mipsNameInv_map (k : Nat) : mipsNameInv (mipsNameMap k) = k := by
  by_cases h : k < 32
  · interval_cases k <;> rfl
  · unfold mipsNameMap; split <;> (try omega)
    unfold mipsNameInv; split <;> first | rfl | omega

theorem mipsNameMap_inv (k : Nat) : mipsNameMap (mipsNameInv k) = k := by
  by_cases h : k < 32
  · interval_cases k <;> rfl
  · unfold mipsNameInv; split <;> (try omega)
    unfold mipsNameMap; split <;> first | rfl | omega

theorem findNameSpt_mipsNames :
    StackNames.findNameSpt mipsNames = mipsNameMap := funext mipsNames_lookup_eq

/-- `backend_config_ok mips32_config mips32_backend_config`. -/
theorem mips32BackendConfigOk : backendConfigOk mips32Config mips32BackendConfig := by
  unfold backendConfigOk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | rfl | skip
  case refine_2 => show 0 < 10; decide
  case refine_4 => decide
  case refine_7 =>
    simp only [DataToWord.confOk, DataToWord.shiftLength, mips32BackendConfig,
      mips32BackendConfigWith, Flapjack.wordShiftAmount]
    decide
  case refine_8 => simp [mips32BackendConfig, mips32BackendConfigWith]
  case refine_9 => simp [mips32BackendConfig, mips32BackendConfigWith, mips32Config]
  case refine_10 => simp [mips32BackendConfig, mips32BackendConfigWith, mips32Config]
  case refine_11 => simp [mips32BackendConfig, mips32BackendConfigWith, mips32Config]
  case refine_12 =>
    simp only [StackRemove.maxStackAlloc, DataToWord.maxHeapLimit, DataToWord.shiftLength,
      mips32BackendConfig, mips32BackendConfigWith, Flapjack.wordShiftAmount]
    decide
  case refine_16 =>
    intro w ⟨h1, h2⟩
    rw [BitVec.sle_iff_toInt_le] at h1 h2
    have m8 : (-8 : BitVec 32).toInt = -8 := by decide
    have p8 : (8 : BitVec 32).toInt = 8 := by decide
    have lo : (-32768 : BitVec 32).toInt = -32768 := by decide
    have hi : (32767 : BitVec 32).toInt = 32767 := by decide
    simp only [asmByteOffsetOkExact, asmOffsetOkExact, mips32Config, asmAligned, lo, hi, m8, p8,
      Nat.pow_zero, Nat.mod_one, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
    exact ⟨⟨by omega, by omega⟩, trivial⟩
  case refine_21 => simp [mips32BackendConfig, mips32BackendConfigWith]
  case refine_22 =>
    rw [show mips32BackendConfig.stackConf.regNames = mipsNames from rfl, findNameSpt_mipsNames]
    exact ⟨Function.LeftInverse.injective mipsNameInv_map,
      fun t => ⟨mipsNameInv t, mipsNameMap_inv t⟩⟩
  case refine_23 =>
    have hf : StackNames.findName (fun key => Flapjack.sptLookup key mipsNames) = mipsNameMap := by
      funext r
      rw [← mipsNames_lookup_eq]
      simp only [StackNames.findName, FLOOKUP]
      cases Flapjack.sptLookup r mipsNames <;> rfl
    simp only [StackNames.namesOkSptHOL, show mips32BackendConfig.stackConf.regNames = mipsNames
      from rfl, hf]
    decide
  case refine_24 => simp [StackProps.fixedNames, mips32Config]
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
    have hv : (BitVec.ofNat 32 (n * (32 / 8))).toInt = n * 4 := by
      rw [BitVec.toInt_eq_toNat_of_lt]
      · simp; omega
      · simp; omega
    have lo : (-32768 : BitVec 32).toInt = -32768 := by decide
    have hi : (32767 : BitVec 32).toInt = 32767 := by decide
    simp only [mips32Config, BitVec.slt_iff_toInt_lt, BitVec.sle_iff_toInt_le, hv, lo, hi,
      Bool.and_eq_true]
    omega

end Flapjack.Compiler.Backend.Mips32Config
