import Flapjack.Compiler.Backend.BackendPasses.Word
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.CakeParser.Frontend

/-! Emit the initial word stage for the pinned explorer regression. -/
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend

def main : IO UInt32 := do
  let source := "datatype t = A | B int; fun f x = case x of A => ~1 | B n => n; val x = f (B 7);"
  let .success ds := Flapjack.CakeParser.Frontend.parseSourceFuel 20000 20000 (ofString source).explode
    | return 1
  let cfg := RiscVConfig.riscvBackendConfigExecutable
  let front := BackendPasses.captureFrontend cfg.sourceConf ds
  let some clos := BackendPasses.captureClosure 20000 cfg.closConf front.closure
    | return 2
  let some bvi := BackendPasses.captureBvi 20000 cfg.bvlConf clos
    | return 3
  let some data := BackendPasses.captureData 20000 bvi
    | return 4
  let some stage := BackendPasses.captureWord64 cfg.dataConf data
    | return 5
  let bytes := BackendPasses.wordReportBytes stage
  (← IO.getStdout).write (ByteArray.mk (bytes.map (fun b => UInt8.ofNat b.toNat)).toArray)
  return 0
