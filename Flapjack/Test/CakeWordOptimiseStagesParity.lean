module

public import Flapjack.Compiler.Backend.BackendPasses.WordOptimise
public import Flapjack.Compiler.Backend.RiscVConfig.Executable
public import Flapjack.Compiler.Encoders.RiscV.Target.Configuration

import all Flapjack.Compiler.Backend.BackendPasses.WordOptimise
import all Flapjack.Compiler.Backend.RiscVConfig.Executable
import all Flapjack.Compiler.Encoders.RiscV.Target.Configuration
public meta import Flapjack.Compiler.Backend.RiscVConfig.Names
public meta import Flapjack.Compiler.Backend.Backend.PrimSrcConfig.Executable
public meta import Flapjack.Compiler.Backend.BviLet.SourceList
public meta import Flapjack.Compiler.Backend.BviToData.CompileSource
public meta import Flapjack.Compiler.Backend.BvlConst.SourceCompile
public meta import Flapjack.Compiler.Backend.BvlHandle.SourceCompile
public meta import Flapjack.Compiler.Backend.ClosToBvl.Compile
public meta import Flapjack.Compiler.Backend.FlatPattern.CompileTotal
public meta import Flapjack.Compiler.Backend.FlatToClos.Compile
public meta import Flapjack.Compiler.Backend.SourceToFlat.CompileExp
public meta import Flapjack.Compiler.Backend.WordBignum.CompileExp
public meta import Flapjack.Compiler.Backend.WordSimp
public meta import Flapjack.Pancake.WordLang.MaxVar
public meta import Flapjack.Compiler.Backend.WordInst.ExecutableInstSelect
public meta import Flapjack.Compiler.Backend.WordAlloc.FullSSA
public meta import Flapjack.Compiler.Backend.WordAlloc.RemoveDead
public meta import Flapjack.Compiler.Backend.WordCse.Transform
public meta import Flapjack.Compiler.Backend.WordCopy
public meta import Flapjack.Compiler.Backend.WordUnreach
public meta import Flapjack.Compiler.Backend.WordToWord.Config
public meta import Flapjack.Compiler.Backend.WordToWord.FastCompile
public meta import Flapjack.Compiler.Backend.RegAlloc.Executable
public meta import Flapjack.Display
public meta import Flapjack.Compiler.Backend.PresLang.Clos
public meta import Flapjack.Compiler.Backend.PresLang.Word

@[expose] public section

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
