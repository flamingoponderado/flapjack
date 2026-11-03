import Flapjack.Compiler.Backend.X64Config.BackendConfig
import Flapjack.Compiler.Backend.BackendProof.ConfigOk
import Flapjack.Compiler.Encoders.X64.Machine.Target
import Mathlib.Tactic.IntervalCases

/-!
# `backend_config_ok` for the x86-64 backend configuration

The x86-64 counterpart of `Flapjack/Compiler/Backend/Arm8Config/BackendProof.lean`:
the 27 conjuncts of HOL `backendProof$backend_config_ok_def`
(`backendProofScript.sml:53-86`) at `Flapjack.Compiler.Encoders.X64.x64Config`
and the configuration Pancake compiles with, `pancake_backend_conf
x64_backend_config` (`compilerScript.sml`; the only difference from
`x64_backend_config` is `data_conf.gc_kind := None`, which no conjunct of
`backend_config_ok` reads).  Flapjack-specific instantiation, so untagged.

The machine-configuration half of `x64_configProofScript.sml` is in
`Flapjack.Compiler.Backend.X64Config.Proofs`; the register-name bijection uses
the explicit `x64NameMap` of `Flapjack.Compiler.Backend.X64Config.Names`.
-/

namespace Flapjack.Compiler.Backend.X64Config

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Encoders.X64

/-- The inverse of `x64NameMap` (Flapjack infrastructure): the fourteen-cycle
`1 → 7 → 3 → 2 → 6 → 9 → 11 → 14 → 4 → 1` and `5 → 8 → 15 → 5`,
`12 → 13 → 12`, identity elsewhere. -/
def x64NameInv (register : Nat) : Nat :=
  match register with
  | 7 => 1 | 6 => 2 | 2 => 3 | 1 => 4 | 8 => 5 | 9 => 6 | 14 => 11 | 13 => 12
  | 12 => 13 | 3 => 7 | 15 => 8 | 11 => 9 | 4 => 14 | 5 => 15
  | r => r

/-- `x64NameInv` is a left inverse of `x64NameMap`: the names map is injective. -/
theorem x64NameInv_map (k : Nat) : x64NameInv (x64NameMap k) = k := by
  by_cases h : k < 16
  · interval_cases k <;> rfl
  · unfold x64NameMap
    split <;> (try omega)
    unfold x64NameInv
    split <;> first | rfl | omega

/-- `x64NameInv` is a right inverse of `x64NameMap`: the names map is surjective. -/
theorem x64NameMap_inv (k : Nat) : x64NameMap (x64NameInv k) = k := by
  by_cases h : k < 16
  · interval_cases k <;> rfl
  · unfold x64NameInv
    split <;> (try omega)
    unfold x64NameMap
    split <;> first | rfl | omega

/-- `findNameSpt` of `x64Names` is the explicit map `x64NameMap`. -/
theorem findNameSpt_x64Names :
    StackNames.findNameSpt x64Names = x64NameMap :=
  funext x64Names_lookup_eq

/-- A small `BitVec.ofNat 64` value's signed reading is that natural number. -/
theorem toInt_ofNat_small {m : Nat} (hm : m < 2 ^ 63) :
    (BitVec.ofNat 64 m).toInt = (m : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have h1 : (BitVec.ofNat 64 m).toNat = m := by rw [BitVec.toNat_ofNat]; omega
  rw [h1]
  have h2 : 2 * m < 2 ^ 64 := by omega
  rw [if_pos h2]

/-- `backend_config_ok` at `x64_config` and `x64_backend_config`. -/
theorem x64BackendConfigOkRaw :
    backendConfigOk x64Config x64BackendConfig := by
  unfold backendConfigOk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | rfl | skip
  case refine_2 => show 0 < 10; decide
  case refine_4 => decide
  case refine_7 =>
    simp only [DataToWord.confOk, DataToWord.shiftLength, x64BackendConfig,
      x64BackendConfigWith, Flapjack.wordShiftAmount]
    decide
  case refine_8 => simp [x64BackendConfig, x64BackendConfigWith, x64Config]
  case refine_9 =>
    intro h
    simp [x64BackendConfig, x64BackendConfigWith] at h
  case refine_10 => simp [x64BackendConfig, x64BackendConfigWith, x64Config]
  case refine_11 => simp [x64BackendConfig, x64BackendConfigWith, x64Config]
  case refine_12 =>
    simp only [StackRemove.maxStackAlloc, DataToWord.maxHeapLimit, DataToWord.shiftLength,
      x64BackendConfig, x64BackendConfigWith, Flapjack.wordShiftAmount]
    decide
  case refine_16 =>
    intro w ⟨h1, h2⟩
    rw [BitVec.sle_iff_toInt_le] at h1 h2
    have m8 : (-8 : BitVec 64).toInt = -8 := by decide
    have p8 : (8 : BitVec 64).toInt = 8 := by decide
    have lo : (x64Min32 : BitVec 64).toInt = -(2 ^ 31 : Int) := by decide
    have hi : (x64Max32 : BitVec 64).toInt = 2 ^ 31 - 1 := by decide
    simp only [asmByteOffsetOkExact, asmOffsetOkExact, x64Config, asmAligned, lo, hi, m8, p8,
      Nat.pow_zero, Nat.mod_one, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
    exact ⟨⟨by omega, by omega⟩, trivial⟩
  case refine_21 => simp [x64BackendConfig, x64BackendConfigWith]
  case refine_22 =>
    rw [show x64BackendConfig.stackConf.regNames = x64Names from rfl, findNameSpt_x64Names]
    exact ⟨Function.LeftInverse.injective x64NameInv_map,
      fun t => ⟨x64NameInv t, x64NameMap_inv t⟩⟩
  case refine_23 =>
    have hf : StackNames.findName (fun key => Flapjack.sptLookup key x64Names) = x64NameMap := by
      funext r
      rw [← x64Names_lookup_eq]
      simp only [StackNames.findName, FLOOKUP]
      cases Flapjack.sptLookup r x64Names <;> rfl
    simp only [StackNames.namesOkSptHOL,
      show x64BackendConfig.stackConf.regNames = x64Names from rfl, hf]
    decide
  case refine_24 =>
    have hf : StackNames.findName (fun key => Flapjack.sptLookup key x64Names) = x64NameMap := by
      funext r
      rw [← x64Names_lookup_eq]
      simp only [StackNames.findName, FLOOKUP]
      cases Flapjack.sptLookup r x64Names <;> rfl
    simp only [StackProps.fixedNames, x64Config]
    rw [show x64BackendConfig.stackConf.regNames = x64Names from rfl, hf]
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
    have h8 : (64 : Nat) / 8 = 8 := by norm_num
    have hm : n * (64 / 8) < 2 ^ 63 := by rw [h8]; omega
    have hv : (BitVec.ofNat 64 (n * (64 / 8))).toInt = (n * (64 / 8) : Int) :=
      toInt_ofNat_small hm
    have lo : (x64Min32 : BitVec 64).toInt = -(2 ^ 31 : Int) := by decide
    have hi : (x64Max32 : BitVec 64).toInt = 2 ^ 31 - 1 := by decide
    simp only [x64Config, hv, lo, hi]
    constructor <;> (simp only [decide_eq_true_eq]; omega)

/-- `backend_config_ok` does not read `data_conf.gc_kind`, so the GC-free
`pancake_backend_conf` record (`pancakeX64BackendConfig`) satisfies it exactly when
`x64BackendConfig` does (Flapjack-specific; no HOL original). -/
theorem backendConfigOk_pancakeX64BackendConfig :
    backendConfigOk x64Config pancakeX64BackendConfig ↔
      backendConfigOk x64Config x64BackendConfig :=
  Iff.rfl

/-- `backend_config_ok x64_config (pancake_backend_conf x64_backend_config)`: the
configuration check for the GC-free configuration that Pancake actually compiles with. -/
theorem x64BackendConfigOk :
    backendConfigOk x64Config pancakeX64BackendConfig :=
  backendConfigOk_pancakeX64BackendConfig.mpr x64BackendConfigOkRaw

end Flapjack.Compiler.Backend.X64Config
