module

public import Flapjack.Compiler.Backend.BackendPasses.Closure
public import Flapjack.Compiler.Backend.RiscVConfig.Executable
public import Flapjack.CakeParser.Frontend

-- Checks below run compiled code from these modules.
public meta import Flapjack.CakeParser.Frontend
public meta import Flapjack.Compiler.Backend.BackendPasses.Closure
public meta import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality
public meta import Flapjack.Compiler.Backend.RiscVConfig.Executable
@[expose] public section

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
