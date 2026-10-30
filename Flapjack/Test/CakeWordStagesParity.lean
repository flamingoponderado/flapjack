import Flapjack.Compiler.Backend.BackendPasses.Word
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.CakeParser.Frontend

/-! The full original comparison is `scripts/check-cake-word-explore.py`.
This check compares the captured WordLang functions with the ordinary
configured compiler path for the same input and display name map. -/
namespace Flapjack.Test.CakeWordStagesParity
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend

private def matchesProduction : Bool := Id.run do
  let source := "datatype t = A | B int; fun f x = case x of A => ~1 | B n => n; val x = f (B 7);"
  let .success ds := Flapjack.CakeParser.Frontend.parseSourceFuel 20000 20000 (ofString source).explode
    | return false
  let cfg := RiscVConfig.riscvBackendConfigExecutable
  let front := BackendPasses.captureFrontend cfg.sourceConf ds
  let some clos := BackendPasses.captureClosure 20000 cfg.closConf front.closure
    | return false
  let some bvi := BackendPasses.captureBvi 20000 cfg.bvlConf clos
    | return false
  let some data := BackendPasses.captureData 20000 bvi
    | return false
  let some word := BackendPasses.captureWord64 cfg.dataConf data
    | return false
  let some (_, _, _, actual, _) :=
      SourceToFlat.compileCakeToWord64ConfiguredFuel 20000 cfg.sourceConf cfg.closConf cfg.bvlConf cfg.dataConf ds
    | return false
  return String.join (PresLang.Word.functions word.names word.functions) ==
    String.join (PresLang.Word.functions word.names actual)

#guard matchesProduction

end Flapjack.Test.CakeWordStagesParity
