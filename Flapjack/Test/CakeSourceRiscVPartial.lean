import Flapjack.Compiler.Backend.SourceToFlat.FromText
import Flapjack.Compiler.Backend.RiscVConfig.Executable

/-! This verifies only the experimental parser-to-backend composition. It does
not establish correspondence to the complete CakeML executable. -/
namespace Flapjack.Test.CakeSourceRiscVPartial
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.SourceToFlat

private def config : Backend.Config :=
  { RiscVConfig.riscvBackendConfigExecutable with
    sourceConf := SourceToFlat.emptyConfig
    closConf := { ClosToBvl.defaultConfig with maxApp := 0, doMti := false, doCall := false, knownConf := none }
    dataConf := ⟨1, 2, 3, 16, false, false, false, false, false, false, .simple⟩ }

#guard match compileUntypedSourceFuel 100 100 100 config [],
    compileCakeToRiscVConfiguredFuel 100 config [] with
  | .success bytes bitmaps _, some (expectedBytes, expectedBitmaps, _) =>
      !bytes.isEmpty && bytes == expectedBytes && bitmaps == expectedBitmaps
  | _, _ => false

end Flapjack.Test.CakeSourceRiscVPartial
