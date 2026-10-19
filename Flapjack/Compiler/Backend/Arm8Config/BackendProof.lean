import Flapjack.Compiler.Backend.Arm8Config.BackendConfig
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

/-- The inverse of `arm8NameMap` (Flapjack infrastructure): the ten-cycle
`0 → 30 → 26 → 25 → 29 → 18 → 4 → 3 → 2 → 1 → 0` reversed, identity elsewhere. -/
def arm8NameInv (register : Nat) : Nat :=
  match register with
  | 30 => 0 | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 18 | 29 => 25
  | 25 => 26 | 18 => 29 | 26 => 30 | r => r

/-- `arm8NameInv` is a left inverse of `arm8NameMap`: the names map is injective. -/
theorem arm8NameInv_map (k : Nat) : arm8NameInv (arm8NameMap k) = k := by
  by_cases h : k < 32
  · interval_cases k <;> rfl
  · unfold arm8NameMap
    split <;> (try omega)
    unfold arm8NameInv
    split <;> first | rfl | omega

/-- `arm8NameInv` is a right inverse of `arm8NameMap`: the names map is surjective. -/
theorem arm8NameMap_inv (k : Nat) : arm8NameMap (arm8NameInv k) = k := by
  by_cases h : k < 32
  · interval_cases k <;> rfl
  · unfold arm8NameInv
    split <;> (try omega)
    unfold arm8NameMap
    split <;> first | rfl | omega

/-- `findNameSpt` of `arm8Names` is the explicit map `arm8NameMap`. -/
theorem findNameSpt_arm8Names :
    StackNames.findNameSpt arm8Names = arm8NameMap :=
  funext arm8Names_lookup_eq

/-- A `BitVec 64` whose `toNat` is below `2 ^ 12` has no bits outside the low twelve,
so `~~~0xFFF` clears it: the condition behind `validImmediate`'s `add`/`sub` range
test `i &&& ~~~0xFFF = 0`. -/
theorem and_not_fff_eq_zero {x : BitVec 64} (hx : x.toNat < 4096) :
    x &&& ~~~(0xFFF : BitVec 64) = 0 := by
  have hx' : x.toNat < 2 ^ 12 := by norm_num; exact hx
  have h1 : x &&& (0xFFF : BitVec 64) = x := by
    rw [BitVec.toNat_eq, BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow hx'
  calc x &&& ~~~(0xFFF : BitVec 64)
      = (x &&& (0xFFF : BitVec 64)) &&& ~~~(0xFFF : BitVec 64) := by rw [h1]
    _ = x &&& ((0xFFF : BitVec 64) &&& ~~~(0xFFF : BitVec 64)) := by rw [BitVec.and_assoc]
    _ = x &&& 0 := by rw [BitVec.and_not_self]
    _ = 0 := BitVec.and_zero

/-- `validImmediate`'s `add`/`sub` test holds for `BitVec.ofNat 64 m` when
`m < 2 ^ 12` (the stack-frame byte offsets `n * (64 / 8)` for `n ≤ 255`). -/
theorem ofNat_and_not_fff_eq_zero {m : Nat} (hm : m < 4096) :
    BitVec.ofNat 64 m &&& ~~~(0xFFF : BitVec 64) = 0 := by
  apply and_not_fff_eq_zero
  rw [BitVec.toNat_ofNat]
  have hpow : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  omega

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
