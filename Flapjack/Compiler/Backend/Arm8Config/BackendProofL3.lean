module

public import Flapjack.Compiler.Backend.Arm8Config.Names
public import Flapjack.Compiler.Backend.Arm8Config.NameLemmas
public import Flapjack.Compiler.Backend.Arm8Config.ProofsL3
public import Flapjack.Compiler.Encoders.Arm8.BitVecLemmas
public import Flapjack.Compiler.Backend.BackendProof.ConfigOk
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# `backend_config_ok` at the L3 ARMv8 configuration

The 27 conjuncts of HOL `backendProof$backend_config_ok_def`
(`backendProofScript.sml:53-86`) at `Flapjack.Compiler.Encoders.Arm8.L3.arm8ConfigL3`
and the configuration Pancake compiles with,
`pancake_backend_conf arm8_backend_config`.  The only field that differs from the
closed-model `arm8Config` is `valid_imm`, so the proof follows
`Arm8Config.BackendProof.arm8BackendConfigOkRaw` with the L3 immediate test.
The register-name and range-test lemmas it shares with the closed-model proof
live in `Arm8Config.Names` and `Arm8/BitVecLemmas.lean`.

The machine-configuration half of `arm8_configProofScript.sml` over the L3
carriers is in `Arm8Config.ProofsL3`.  Flapjack-specific instantiation, so untagged.

This proof is a near-duplicate of `Arm8Config.BackendProof.arm8BackendConfigOkRaw`
in the closed model: `arm8ConfigL3` and `arm8Config` have the same sixteen field
values except `encode` (the L3 lowering versus the closed subset encoder) and
`validImm` (`arm8ValidImmediate` versus `validImmediate`), and
`backend_config_ok` reads only `validImm` of the two.  Keep the two proofs in
step: a change to either configuration or to `backend_config_ok` must be made in
both files.
-/

namespace Flapjack.Compiler.Backend.Arm8Config

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Encoders.Arm8.L3

/-- `backend_config_ok` at `arm8_config` and `arm8_backend_config`, over the L3
configuration. -/
theorem arm8BackendConfigOkRawL3 :
    backendConfigOk arm8ConfigL3 arm8BackendConfig := by
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
  case refine_9 => simp [arm8BackendConfig, arm8BackendConfigWith, arm8ConfigL3]
  case refine_10 => simp [arm8BackendConfig, arm8BackendConfigWith, arm8ConfigL3]
  case refine_11 => simp [arm8BackendConfig, arm8BackendConfigWith, arm8ConfigL3]
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
    simp only [asmByteOffsetOkExact, asmOffsetOkExact, arm8ConfigL3, asmAligned, lo, hi, m8, p8,
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
  case refine_24 => simp [StackProps.fixedNames, arm8ConfigL3]
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
    have h8 : (64 : Nat) / 8 = 8 := by norm_num
    have hm : n * (64 / 8) < 4096 := by rw [h8]; omega
    have hv : BitVec.ofNat 64 (n * (64 / 8)) &&& ~~~(0xFFF : BitVec 64) = 0 :=
      Flapjack.Compiler.Encoders.Arm8.ofNat_and_not_fff_eq_zero hm
    simp only [arm8ConfigL3, arm8ValidImmediate, hv, decide_true, Bool.true_or]
    exact ⟨trivial, trivial⟩

/-- `backend_config_ok` does not read `data_conf.gc_kind`, so the GC-free
`pancake_backend_conf` record satisfies it exactly when `arm8BackendConfig` does
(Flapjack-specific; no HOL original). -/
theorem backendConfigOk_pancakeArm8BackendConfigL3 :
    backendConfigOk arm8ConfigL3 pancakeArm8BackendConfig ↔
      backendConfigOk arm8ConfigL3 arm8BackendConfig :=
  Iff.rfl

/-- `backend_config_ok arm8_config (pancake_backend_conf arm8_backend_config)` at the
L3 configuration. -/
theorem arm8BackendConfigOkL3 :
    backendConfigOk arm8ConfigL3 pancakeArm8BackendConfig :=
  backendConfigOk_pancakeArm8BackendConfigL3.mpr arm8BackendConfigOkRawL3

end Flapjack.Compiler.Backend.Arm8Config
