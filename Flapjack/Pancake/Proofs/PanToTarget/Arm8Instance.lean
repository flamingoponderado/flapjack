import Flapjack.Pancake.Proofs.PanToTarget.AssemblyTop
import Flapjack.Compiler.Backend.Arm8Config.BackendProof
import Flapjack.Compiler.Backend.Arm8Config.Proofs

/-!
# `pan_to_target_compile_semantics` at the closed ARMv8 target

The tagged `panToTargetCompileSemantics` instantiated at the closed ARMv8 machine
model with Pancake's backend configuration.  `backend_config_ok`, `mc_conf_ok`
and `mc_init_ok` are discharged unconditionally; the encoder-correctness
obligation is `arm8EncoderCorrect` from `Machine/Complete.lean`.

This is a statement about the logical compiler `compile_prog_max`; it does not
establish that the executed `flapjack-compile` route computes that function.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL
open Flapjack.Compiler.Backend.Arm8Config Flapjack.Compiler.Encoders.Arm8

/-- The top theorem's configuration-only heap bound, decided for Pancake's ARMv8
configuration (Flapjack-specific; no HOL original). -/
theorem arm8PancakeHeapLimit_lt :
    (wordSemBytesInWord : BitVec 64).toNat *
        (2 * DataToWord.maxHeapLimit 64
          (Flapjack.Compiler.pancakeBackendConf arm8BackendConfig).dataConf - 1) < 2 ^ 64 := by
  simp only [DataToWord.maxHeapLimit, DataToWord.shiftLength, arm8BackendConfig,
    arm8BackendConfigWith, Flapjack.Compiler.pancakeBackendConf, Flapjack.wordShiftAmount,
    wordSemBytesInWord]
  decide

end Flapjack.Pancake.Proofs.PanToTarget
