import Flapjack.Compiler.Backend.BackendPasses.WordOptimise
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration

/-! The full original comparison is `scripts/check-cake-word-optimise-explore.py`.
This small case compares the captured allocation with the normal executable
word-to-word compiler, including the remaining oracle. -/
namespace Flapjack.Test.CakeWordOptimiseStagesParity
open Flapjack Flapjack.Compiler.Backend

private def matchesProduction : Bool := Id.run do
  let config := RiscVConfig.riscvBackendConfigExecutable.wordToWordConf
  let asm := Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig
  let code : BackendPasses.WordFunctions := [(8, 0, .return 0 [])]
  let input : BackendPasses.WordStage := ⟨code, .ln⟩
  let stages := BackendPasses.captureWordOptimise asm config input
  let (remaining, output) := WordToWord.compileWith RegAlloc.regAllocExecutable config asm code
  return decide (stages.remainingOracle = remaining) &&
    String.join (PresLang.Word.functions .ln stages.allocated) ==
      String.join (PresLang.Word.functions .ln output)

#guard matchesProduction

end Flapjack.Test.CakeWordOptimiseStagesParity
