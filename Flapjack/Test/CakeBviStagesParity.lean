import Flapjack.Compiler.Backend.BackendPasses.Bvi
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.CakeParser.Frontend

/-! The complete byte output is compared against pinned CakeML by
`scripts/check-cake-bvi-explore.py`. This checks that capture succeeds and
agrees with the production BVI code, names, and fresh-name counters for the
same input. -/
namespace Flapjack.Test.CakeBviStagesParity
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend

private def captured : Bool := Id.run do
  let source := "datatype t = A | B int; fun f x = case x of A => ~1 | B n => n; val x = f (B 7);"
  let .success ds := Flapjack.CakeParser.Frontend.parseSourceFuel 20000 20000 (ofString source).explode
    | return false
  let cfg := RiscVConfig.riscvBackendConfigExecutable
  let front := BackendPasses.captureFrontend cfg.sourceConf ds
  let some clos := BackendPasses.captureClosure 20000 cfg.closConf front.closure
    | return false
  let some stages := BackendPasses.captureBvi 20000 cfg.bvlConf clos
    | return false
  let some (_, actualClos, actualBvl, actualCode, actualNames) :=
      SourceToFlat.compileCakeToBviConfiguredFuel 20000 cfg.sourceConf cfg.closConf cfg.bvlConf ds
    | return false
  return stages.inlineBvi == actualCode &&
    decide (stages.productionNames = actualNames) &&
    stages.closureConfig.start == actualClos.start &&
    stages.closureConfig.nextLoc == actualClos.nextLoc &&
    stages.bvlConfig.nextName1 == actualBvl.nextName1 &&
    stages.bvlConfig.nextName2 == actualBvl.nextName2 &&
    stages.bvlConfig.nextName3 == actualBvl.nextName3

#guard captured

end Flapjack.Test.CakeBviStagesParity
