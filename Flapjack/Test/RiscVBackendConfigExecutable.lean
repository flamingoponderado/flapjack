import Flapjack.Compiler.Backend.RiscVConfig.Executable

/-! Compiler regression for the original tagged backend constant. This def
failed dependsOnNoncomputable before the unconditional compiler realization;
it deliberately consumes the original declarations, not the executable mirror.
The whole-record kernel equality provides field correspondence. -/
namespace Flapjack.Test.RiscVBackendConfigExecutable
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig

private def originalConsumer : Backend.Config :=
  Flapjack.Compiler.pancakeBackendConf riscvBackendConfig

private def observation : Bool :=
  originalConsumer.dataConf.gcKind == .none &&
  originalConsumer.dataConf.tagBits == 4 &&
  originalConsumer.dataConf.hasDiv == true &&
  originalConsumer.sourceConf.next.tidx == 2 &&
  originalConsumer.sourceConf.next.eidx == 4 &&
  originalConsumer.stackConf.jump == false &&
  originalConsumer.stackConf.perfCalls == false &&
  originalConsumer.labConf.initClock == 5 &&
  originalConsumer.labConf.hashSize == 104729

def runChecks : IO Bool := do
  unless observation do
    throw (IO.userError "compiled original Pancake RISC-V configuration changed")
  IO.println "PASS executable original Pancake RISC-V backend configuration"
  pure true

end Flapjack.Test.RiscVBackendConfigExecutable
