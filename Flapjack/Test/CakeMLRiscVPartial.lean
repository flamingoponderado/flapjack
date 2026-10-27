import Flapjack.Compiler.Backend.SourceToFlat.ToRiscV
import Flapjack.Compiler.Backend.RiscVConfig.Executable

/-! Smoke check of the explicitly restricted source-AST to RISC-V route. -/
namespace Flapjack.Test.CakeMLRiscVPartial
open Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString

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

#guard match SourceToFlat.compileCakeToRiscVNamedNoOptsFuel 100 testConfig [],
    SourceToFlat.compileCakeToRiscVInlineFuel 100 testConfig [] with
  | some (bytes, bitmaps, _), some (inlineBytes, inlineBitmaps, _) =>
      bytes == inlineBytes && bitmaps == inlineBitmaps
  | _, _ => false

private def optimizedConfig : Backend.Config :=
  { testConfig with closConf := { testConfig.closConf with maxApp := 2, doMti := true } }

#guard match SourceToFlat.compileCakeToRiscVOptimizedFuel 100 8 100 false optimizedConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (bytes, bitmaps, _) => !bytes.isEmpty && !bitmaps.isEmpty
  | none => false

#guard match SourceToFlat.compileCakeToRiscVOptimizedFuel 100 8 100 false
    { optimizedConfig with closConf := { optimizedConfig.closConf with doCall := true } }
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (bytes, bitmaps, _) => !bytes.isEmpty && !bitmaps.isEmpty
  | none => false

#guard match SourceToFlat.compileCakeToRiscVConfiguredFuel 100
    { optimizedConfig with closConf := { optimizedConfig.closConf with doCall := true, knownConf := some (ClosKnown.defaultConfig 2) }, bvlConf := BvlToBvi.defaultConfig }
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (bytes, bitmaps, _) => !bytes.isEmpty && !bitmaps.isEmpty
  | none => false

-- These operations are AST-level primitives; the ordinary source parser does
-- not expose the unsafe XOR operation. Check the actual configured backend.
#guard match SourceToFlat.compileCakeToRiscVConfiguredFuel 100
    { optimizedConfig with closConf := { optimizedConfig.closConf with doCall := true, knownConf := some (ClosKnown.defaultConfig 2) }, bvlConf := BvlToBvi.defaultConfig }
    [.dlet Flapjack.Misc.Location.unknownLoc .pany
      (.app .configGC [.lit (.intLit 0), .lit (.intLit 0)])] with
  | some (bytes, _, _) => !bytes.isEmpty
  | none => false

#guard match SourceToFlat.compileCakeToRiscVConfiguredFuel 100
    { optimizedConfig with closConf := { optimizedConfig.closConf with doCall := true, knownConf := some (ClosKnown.defaultConfig 2) }, bvlConf := BvlToBvi.defaultConfig }
    [.dlet Flapjack.Misc.Location.unknownLoc .pany
      (.app .xorAw8StrUnsafe [(.app .aw8alloc [.lit (.intLit 3), .lit (.word8 0)]), .lit (.strLit (ofString "abc"))])] with
  | some (bytes, _, _) => !bytes.isEmpty
  | none => false

end Flapjack.Test.CakeMLRiscVPartial
