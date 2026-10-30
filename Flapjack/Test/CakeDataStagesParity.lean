import Flapjack.Compiler.Backend.BackendPasses.Data
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.CakeParser.Frontend

/-! `scripts/check-cake-data-explore.py` compares the entire captured output
with pinned CakeML. This guard checks that the capture succeeds for that input. -/
namespace Flapjack.Test.CakeDataStagesParity
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend

private def captured : Bool := Id.run do
  let source := "datatype t = A | B int; fun f x = case x of A => ~1 | B n => n; val x = f (B 7);"
  let .success ds := Flapjack.CakeParser.Frontend.parseSourceFuel 20000 20000 (ofString source).explode
    | return false
  let cfg := RiscVConfig.riscvBackendConfigExecutable
  let front := BackendPasses.captureFrontend cfg.sourceConf ds
  let some clos := BackendPasses.captureClosure 20000 cfg.closConf front.closure
    | return false
  let some bvi := BackendPasses.captureBvi 20000 cfg.bvlConf clos
    | return false
  return (BackendPasses.captureData 20000 bvi).isSome

#guard captured

end Flapjack.Test.CakeDataStagesParity
