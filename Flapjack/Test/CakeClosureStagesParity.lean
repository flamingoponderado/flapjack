import Flapjack.Compiler.Backend.BackendPasses.Closure
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.CakeParser.Frontend

/-! The complete captured bytes are compared with pinned CakeML by
`scripts/check-cake-closure-explore.py`. This guard checks that the same
regression input reaches the captured BVL stage without exhausting fuel. -/
namespace Flapjack.Test.CakeClosureStagesParity
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend

private def captured : Bool :=
  let source := "datatype t = A | B int; fun f x = case x of A => ~1 | B n => n; val x = f (B 7);"
  match Flapjack.CakeParser.Frontend.parseSourceFuel 20000 20000 (ofString source).explode with
  | .success ds =>
      let cfg := RiscVConfig.riscvBackendConfigExecutable
      let front := BackendPasses.captureFrontend cfg.sourceConf ds
      (BackendPasses.captureClosure 20000 cfg.closConf front.closure).isSome
  | _ => false

#guard captured

end Flapjack.Test.CakeClosureStagesParity
