module

public import Flapjack.Compiler.Backend.X64Config.Names
public import Flapjack.Compiler.Backend.Backend
public import Flapjack.Compiler.Backend.Backend.PrimSrcConfig
public import Flapjack.Compiler.Backend.Backend.PrimSrcConfig.Executable
public import Flapjack.Compiler.Backend.ClosToBvl.Config
public import Flapjack.Compiler.Backend.BvlToBvi.Config
public import Flapjack.Compiler.Backend.PresLang.Config
public import Flapjack.Compiler.Compiler

@[expose] public section

/-!
# The x86-64 backend configuration

CakeML's `x64_backend_config` (`cakeml/compiler/backend/x64/x64_configScript.sml`):
the default `clos_conf` and `bvl_conf`, `tag_bits := 4`, `len_bits := 4`,
`pad_bits := 2`, `len_size := 32`, `has_div := false`, `has_longdiv := true`,
`has_fp_ops := true`, `has_fp_tern := false`, little-endian data, no GC,
`reg_alg := 2`, `jump := true`, `x64_names`, and CakeML's `lab_conf`.
-/

namespace Flapjack.Compiler.Backend.X64Config
open Flapjack.Compiler.Backend

/-- The x86-64 backend configuration over a given source configuration. -/
def x64BackendConfigWith (sourceConf : SourceToFlat.Config) : Backend.Config where
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
      hasDiv := false, hasLongdiv := true, hasFpOps := true, hasFpTern := false,
      be := false, callEmptyFfi := false, gcKind := .simple }
  wordToWordConf := { regAlg := 2, colOracle := [] }
  wordConf := { bitmapsLength := 0, stackFrameSize := .ln }
  stackConf := { jump := true, regNames := x64Names, perfCalls := false }
  labConf :=
    { pos := 0, ffiNames := none, labels := .ln, secPosLen := [], initClock := 5,
      hashSize := 104729, shmemExtra := [] }
  symbols := []
  tapConf := PresLang.defaultTapConfig
  exported := []

/-- The x86-64 backend configuration. -/
noncomputable def x64BackendConfig : Backend.Config :=
  x64BackendConfigWith Backend.primSrcConfig

/-- `x64BackendConfig` with the executable primitive-source configuration. -/
def x64BackendConfigExecutable : Backend.Config :=
  x64BackendConfigWith Backend.primSrcConfigExecutable

@[csimp] theorem x64BackendConfig_eq_executable :
    x64BackendConfig = x64BackendConfigExecutable := by
  unfold x64BackendConfig x64BackendConfigExecutable
  rw [Backend.primSrcConfig_eq_executable]

/-- The configuration Pancake compiles with: `pancake_backend_conf` (no garbage
collector) of `x64BackendConfig`. -/
def pancakeX64BackendConfig : Backend.Config :=
  Flapjack.Compiler.pancakeBackendConf x64BackendConfig

end Flapjack.Compiler.Backend.X64Config
