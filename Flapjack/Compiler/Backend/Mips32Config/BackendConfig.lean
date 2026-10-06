import Flapjack.Compiler.Backend.Mips32Config.Names
import Flapjack.Compiler.Backend.Backend
import Flapjack.Compiler.Backend.Backend.PrimSrcConfig
import Flapjack.Compiler.Backend.Backend.PrimSrcConfig.Executable
import Flapjack.Compiler.Backend.ClosToBvl.Config
import Flapjack.Compiler.Backend.BvlToBvi.Config
import Flapjack.Compiler.Backend.PresLang.Config
import Flapjack.Compiler.Compiler

/-!
# The MIPS32 (Ziren) backend configuration

CakeML's `mips_backend_config` (`cakeml/compiler/backend/mips/mips_configScript.sml`) with
little-endian data (`be := false`), because Ziren's guest is `mipsel`. Every other field is
CakeML's MIPS value. Not HOL's `mips_backend_config` (which is big-endian), so untagged.
-/

namespace Flapjack.Compiler.Backend.Mips32Config
open Flapjack.Compiler.Backend

/-- The MIPS32 backend configuration over a given source configuration. -/
def mips32BackendConfigWith (sourceConf : SourceToFlat.Config) : Backend.Config where
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
  stackConf := { jump := false, regNames := mipsNames, perfCalls := false }
  labConf :=
    { pos := 0, ffiNames := none, labels := .ln, secPosLen := [], initClock := 5,
      hashSize := 104729, shmemExtra := [] }
  symbols := []
  tapConf := PresLang.defaultTapConfig
  exported := []

/-- The MIPS32 backend configuration. -/
noncomputable def mips32BackendConfig : Backend.Config :=
  mips32BackendConfigWith Backend.primSrcConfig

/-- `mips32BackendConfig` with the executable primitive-source configuration. -/
def mips32BackendConfigExecutable : Backend.Config :=
  mips32BackendConfigWith Backend.primSrcConfigExecutable

@[csimp] theorem mips32BackendConfig_eq_executable :
    mips32BackendConfig = mips32BackendConfigExecutable := by
  unfold mips32BackendConfig mips32BackendConfigExecutable
  rw [Backend.primSrcConfig_eq_executable]

/-- The configuration Pancake compiles with: `pancake_backend_conf` (no garbage collector)
of `mips32BackendConfig`. -/
def pancakeMips32BackendConfig : Backend.Config :=
  Flapjack.Compiler.pancakeBackendConf mips32BackendConfig

end Flapjack.Compiler.Backend.Mips32Config
