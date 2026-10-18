import Flapjack.Compiler.Backend.Arm8Config.Names
import Flapjack.Compiler.Backend.Backend
import Flapjack.Compiler.Backend.Backend.PrimSrcConfig
import Flapjack.Compiler.Backend.Backend.PrimSrcConfig.Executable
import Flapjack.Compiler.Backend.ClosToBvl.Config
import Flapjack.Compiler.Backend.BvlToBvi.Config
import Flapjack.Compiler.Backend.PresLang.Config
import Flapjack.Compiler.Compiler

/-!
# The ARMv8 (AArch64) backend configuration

CakeML's `arm8_backend_config`
(`cakeml/compiler/backend/arm8/arm8_configScript.sml`), with little-endian data and the
64-bit data layout (`tag_bits := 4`, `len_bits := 4`, `pad_bits := 2`, `len_size := 32`).
Every other field is CakeML's ARMv8 value.
-/

namespace Flapjack.Compiler.Backend.Arm8Config
open Flapjack.Compiler.Backend

/-- The ARMv8 backend configuration over a given source configuration. -/
def arm8BackendConfigWith (sourceConf : SourceToFlat.Config) : Backend.Config where
  sourceConf := sourceConf
  closConf :=
    { nextLoc := 0, start := 1, doMti := true,
      knownConf := some
        { inlineMaxBodySize := 88, inlineFactor := 8, initialInlineFactor := 8,
          valApproxSpt := .ln },
      doCall := true, callState := (.ln, []), maxApp := 10 }
  bvlConf :=
    { inlineSizeLimit := 10, expCut := 1000, splitMainAtSeq := true,
      nextName1 := 73, nextName2 := 74, nextName3 := 75,
      doTailrec := true, doTmc := true, inlines := .ln, bviInlines := .ln }
  dataConf :=
    { tagBits := 4, lenBits := 4, padBits := 2, lenSize := 32,
      hasDiv := true, hasLongdiv := false, hasFpOps := false, hasFpTern := false,
      be := false, callEmptyFfi := false, gcKind := .simple }
  wordToWordConf := { regAlg := 2, colOracle := [] }
  wordConf := { bitmapsLength := 0, stackFrameSize := .ln }
  stackConf := { jump := false, regNames := arm8Names, perfCalls := false }
  labConf :=
    { pos := 0, ffiNames := none, labels := .ln, secPosLen := [], initClock := 5,
      hashSize := 104729, shmemExtra := [] }
  symbols := []
  tapConf := PresLang.defaultTapConfig
  exported := []

/-- The ARMv8 backend configuration. -/
noncomputable def arm8BackendConfig : Backend.Config :=
  arm8BackendConfigWith Backend.primSrcConfig

/-- `arm8BackendConfig` with the executable primitive-source configuration. -/
def arm8BackendConfigExecutable : Backend.Config :=
  arm8BackendConfigWith Backend.primSrcConfigExecutable

@[csimp] theorem arm8BackendConfig_eq_executable :
    arm8BackendConfig = arm8BackendConfigExecutable := by
  unfold arm8BackendConfig arm8BackendConfigExecutable
  rw [Backend.primSrcConfig_eq_executable]

/-- The configuration Pancake compiles with: `pancake_backend_conf` (no garbage collector)
of `arm8BackendConfig`. -/
def pancakeArm8BackendConfig : Backend.Config :=
  Flapjack.Compiler.pancakeBackendConf arm8BackendConfig

end Flapjack.Compiler.Backend.Arm8Config
