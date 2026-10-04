import Flapjack.Compiler.Backend.RiscVConfig.Names
import Flapjack.Compiler.Backend.Backend
import Flapjack.Compiler.Backend.Backend.PrimSrcConfig
import Flapjack.Compiler.Backend.ClosToBvl.Config
import Flapjack.Compiler.Backend.BvlToBvi.Config
import Flapjack.Compiler.Backend.PresLang.Config
import Flapjack.HolRef

/-!
# `riscv_configScript.sml`: `riscv_backend_config`

The RISC-V compiler configuration. HOL builds the definition from SML quotations
(`riscv_configScript.sml:46-53`); the `clos_conf`/`bvl_conf` quotations are the
`EVAL`uated `clos_to_bvl$default_config`/`bvl_to_bvi$default_config`, so the
definition's body (captured in `scripts/hol-probes/riscv_backend_config_probe.out`)
contains those literal records, which are spelled out here.
-/

namespace Flapjack.Compiler.Backend.RiscVConfig

/-- HOL `riscv_backend_config_def` (`riscv_configScript.sml:56-70`), field for field as the
captured definition body: the evaluated `clos_to_bvl`/`bvl_to_bvi` default records, the
RISC-V data (`gc_kind := Simple`), word-to-word, word, stack and lab configurations,
empty symbols/exports and the default tap configuration. -/
@[hol "cakeml/compiler/backend/riscv/riscv_configScript.sml" "riscv_backend_config_def"]
noncomputable def riscvBackendConfig : Backend.Config where
  sourceConf := Backend.primSrcConfig
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
  wordToWordConf := { regAlg := 3, colOracle := [] }
  wordConf := { bitmapsLength := 0, stackFrameSize := .ln }
  stackConf := { jump := false, regNames := riscvNames, perfCalls := false }
  labConf :=
    { pos := 0, ffiNames := none, labels := .ln, secPosLen := [], initClock := 5,
      hashSize := 104729, shmemExtra := [] }
  symbols := []
  tapConf := PresLang.defaultTapConfig
  exported := []

/-- The literal closure configuration is the tagged `clos_to_bvl$default_config`, as
HOL's `EVAL` splice states (Flapjack sanity check; no HOL declaration). -/
theorem riscvBackendConfig_closConf : riscvBackendConfig.closConf = ClosToBvl.defaultConfig :=
  rfl

/-- The literal BVL configuration is the tagged `bvl_to_bvi$default_config`, as HOL's
`EVAL` splice states (Flapjack sanity check; no HOL declaration). -/
theorem riscvBackendConfig_bvlConf : riscvBackendConfig.bvlConf = BvlToBvi.defaultConfig :=
  rfl

end Flapjack.Compiler.Backend.RiscVConfig
