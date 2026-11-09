import Flapjack.Compiler.Backend.Arm8Config.Names
import Flapjack.Compiler.Backend.Arm8Config.NameLemmas
import Flapjack.Compiler.Backend.Arm8Config.BackendConfig
import Flapjack.Compiler.Encoders.Arm8.BitVecLemmas
import Flapjack.Compiler.Backend.Arm8Config.Proofs
import Flapjack.Compiler.Backend.BackendProof.ConfigOk
import Mathlib.Tactic.IntervalCases

/-!
# `backend_config_ok` for the ARMv8 (AArch64) backend configuration

The ARMv8 counterpart of `Flapjack/Compiler/Backend/Mips32Config/Proofs.lean`'s
`mips32BackendConfigOk`: the 27 conjuncts of HOL
`backendProof$backend_config_ok_def` (`backendProofScript.sml:53-86`) at
`Flapjack.Compiler.Encoders.Arm8.arm8Config` and the configuration Pancake compiles
with, `pancake_backend_conf arm8_backend_config` (`compilerScript.sml:744-747`; the
only difference from `arm8_backend_config` is `data_conf.gc_kind := None`, which no
conjunct of `backend_config_ok` reads). Flapjack-specific instantiation, so untagged.

The machine-configuration half of `arm8_configProofScript.sml` is in
`Flapjack.Compiler.Backend.Arm8Config.Proofs`; the register-name bijection uses the
explicit `arm8Names` map of `Flapjack.Compiler.Backend.Arm8Config.Names`.
-/

namespace Flapjack.Compiler.Backend.Arm8Config

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Encoders.Arm8

/-- `backend_config_ok` at `arm8_config` and `arm8_backend_config`. -/
theorem arm8BackendConfigOkRaw :
    backendConfigOk arm8Config arm8BackendConfig := by
  unfold backendConfigOk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | rfl | skip
  case refine_2 => show 0 < 10; decide
  case refine_4 => decide
  case refine_7 =>
    simp only [DataToWord.confOk, DataToWord.shiftLength, arm8BackendConfig,
      arm8BackendConfigWith, Flapjack.wordShiftAmount]
    decide
  case refine_8 => simp [arm8BackendConfig, arm8BackendConfigWith]
  case refine_9 => simp [arm8BackendConfig, arm8BackendConfigWith, arm8Config]
  case refine_10 => simp [arm8BackendConfig, arm8BackendConfigWith, arm8Config]
  case refine_11 => simp [arm8BackendConfig, arm8BackendConfigWith, arm8Config]
  case refine_12 =>
    simp only [StackRemove.maxStackAlloc, DataToWord.maxHeapLimit, DataToWord.shiftLength,
      arm8BackendConfig, arm8BackendConfigWith, Flapjack.wordShiftAmount]
    decide
  case refine_16 =>
    intro w ⟨h1, h2⟩
    rw [BitVec.sle_iff_toInt_le] at h1 h2
    have m8 : (-8 : BitVec 64).toInt = -8 := by decide
    have p8 : (8 : BitVec 64).toInt = 8 := by decide
    have lo : (-256 : BitVec 64).toInt = -256 := by decide
    have hi : (4095 : BitVec 64).toInt = 4095 := by decide
    simp only [asmByteOffsetOkExact, asmOffsetOkExact, arm8Config, asmAligned, lo, hi, m8, p8,
      Nat.pow_zero, Nat.mod_one, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
    exact ⟨⟨by omega, by omega⟩, trivial⟩
  case refine_21 => simp [arm8BackendConfig, arm8BackendConfigWith]
  case refine_22 =>
    rw [show arm8BackendConfig.stackConf.regNames = arm8Names from rfl, findNameSpt_arm8Names]
    exact ⟨Function.LeftInverse.injective arm8NameInv_map,
      fun t => ⟨arm8NameInv t, arm8NameMap_inv t⟩⟩
  case refine_23 =>
    have hf : StackNames.findName (fun key => Flapjack.sptLookup key arm8Names) = arm8NameMap := by
      funext r
      rw [← arm8Names_lookup_eq]
      simp only [StackNames.findName, FLOOKUP]
      cases Flapjack.sptLookup r arm8Names <;> rfl
    simp only [StackNames.namesOkSptHOL,
      show arm8BackendConfig.stackConf.regNames = arm8Names from rfl, hf]
    decide
  case refine_24 => simp [StackProps.fixedNames, arm8Config]
  -- `storeOffset s = 0 - wordOffset (storePos s) = -(8 * storePos s)` and
  -- `storePos s ≤ 48`, so every store offset lies in `[-384, 0]`, inside both
  -- ARMv8 bounds `(-4351, 4350)`; `asmAligned 0` holds trivially.
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
  -- `n ≤ 255` gives the byte offset `n * (64 / 8) ≤ 2040 < 2 ^ 12`, so
  -- `validImmediate`'s range test `i &&& ~~~0xFFF = 0` holds for `add` and `sub`.
  case refine_27 =>
    intro n hn
    simp only [StackRemove.maxStackAlloc] at hn
    have h8 : (64 : Nat) / 8 = 8 := by norm_num
    have hm : n * (64 / 8) < 4096 := by rw [h8]; omega
    have hv : BitVec.ofNat 64 (n * (64 / 8)) &&& ~~~(0xFFF : BitVec 64) = 0 :=
      ofNat_and_not_fff_eq_zero hm
    simp only [arm8Config, validImmediate, hv, decide_true, Bool.true_or]
    exact ⟨trivial, trivial⟩

/-- `backend_config_ok` does not read `data_conf.gc_kind`, so the GC-free
`pancake_backend_conf` record (`pancakeArm8BackendConfig`) satisfies it exactly when
`arm8BackendConfig` does (Flapjack-specific; no HOL original). -/
theorem backendConfigOk_pancakeArm8BackendConfig :
    backendConfigOk arm8Config pancakeArm8BackendConfig ↔
      backendConfigOk arm8Config arm8BackendConfig :=
  Iff.rfl

/-- `backend_config_ok arm8_config (pancake_backend_conf arm8_backend_config)`: the
configuration check for the GC-free configuration that Pancake actually compiles with. -/
theorem arm8BackendConfigOk :
    backendConfigOk arm8Config pancakeArm8BackendConfig :=
  backendConfigOk_pancakeArm8BackendConfig.mpr arm8BackendConfigOkRaw

end Flapjack.Compiler.Backend.Arm8Config
