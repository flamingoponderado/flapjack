import Flapjack.Compiler.Backend.BackendPasses.Data
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.CakeParser.Frontend

/-! Emit the DataLang stages for the pinned explorer regression. -/
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
  let some stages := BackendPasses.captureData 20000 bvi
    | return 4
  let bytes := BackendPasses.dataReportBytes stages
  (← IO.getStdout).write (ByteArray.mk (bytes.map (fun b => UInt8.ofNat b.toNat)).toArray)
  return 0
