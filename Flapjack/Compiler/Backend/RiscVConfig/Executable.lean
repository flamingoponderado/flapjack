import Flapjack.Compiler.Backend.RiscVConfig.BackendConfig
import Flapjack.Compiler.Backend.Backend.PrimSrcConfig.Executable
import Flapjack.Compiler.Compiler

/-! Executable realization of the reviewed native backend configuration.
The existing tagged primitive-source equality eliminates its unused HOL ARB
store. This whole-record compiler equality has no independently named original.
The tagged definitions and their original domains are retained. -/
namespace Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend Flapjack.Basis.Pure.MlString

/-- Every field of the full reviewed backend record, made executable. -/
def riscvBackendConfigExecutable : Backend.Config where

  sourceConf := Backend.primSrcConfigExecutable
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
      hasDiv := true, hasLongdiv := false,
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


/-- Unconditional whole-record realization via the tagged primitive-source
closed-form equality, rather than a different choice of arbitrary store. -/
@[csimp] theorem riscvBackendConfig_eq_executable :
    riscvBackendConfig = riscvBackendConfigExecutable := by
  unfold riscvBackendConfig riscvBackendConfigExecutable
  rw [Backend.primSrcConfig_eq_executable]


/-- The complete Pancake/RISC-V configuration composes the two reviewed
original declarations. Compilation uses the whole-record equality above. -/
def pancakeRiscVBackendConfig : Backend.Config :=
  Flapjack.Compiler.pancakeBackendConf riscvBackendConfig

/-- Whole-record composition, without independently chosen field defaults. -/
theorem pancakeRiscVBackendConfig_eq :
    pancakeRiscVBackendConfig = Flapjack.Compiler.pancakeBackendConf riscvBackendConfig := rfl

end Flapjack.Compiler.Backend.RiscVConfig
