import Flapjack.Compiler.Backend.SourceToFlat.ToRiscV
import Flapjack.Compiler.Backend.RiscVConfig.Executable

/-! Smoke check of the explicitly restricted source-AST to RISC-V route. -/
namespace Flapjack.Test.CakeMLRiscVPartial
open Flapjack.Compiler.Backend

private def testConfig : Backend.Config :=
  { RiscVConfig.riscvBackendConfigExecutable with
    sourceConf := SourceToFlat.emptyConfig
    closConf := { ClosToBvl.defaultConfig with maxApp := 0, doMti := false, doCall := false, knownConf := none }
    dataConf := ⟨1, 2, 3, 16, false, false, false, false, false, false, .simple⟩ }

#guard match SourceToFlat.compileCakeToRiscVNoOptsFuel 100 testConfig .ln [] with
  | some (bytes, bitmaps, _) => bytes.length == 15012 && bitmaps.length == 65
  | none => false

#guard match SourceToFlat.compileCakeToRiscVNoOptsFuel 100 testConfig .ln [],
    SourceToFlat.compileCakeToRiscVNamedNoOptsFuel 100 testConfig [] with
  | some (bytes, bitmaps, _), some (namedBytes, namedBitmaps, _) =>
      bytes == namedBytes && bitmaps == namedBitmaps
  | _, _ => false

end Flapjack.Test.CakeMLRiscVPartial
