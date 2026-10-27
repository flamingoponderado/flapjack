import Flapjack.Compiler.Backend.SourceToFlat.FromText
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.RiscV.CakeArtifactFormat
import Flapjack.Compiler.Inference.Infer.Diagnostics

/-! Experimental CakeML source-to-RISC-V command. The frontend and backend
are still bounded ports, the original diagnostics and full CLI are incomplete,
and final output parity with CakeML has not been established. -/
namespace Flapjack.CakeMain
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.Basis.Pure.MlString

structure Options where
  excludePrelude : Bool := false
  skipTypeInference : Bool := false

private def usage : String :=
  "Usage: cake [--target=riscv] [--exclude_prelude=true|false] " ++
  "[--skip_type_inference=true|false] < input_file\n" ++
  "Experimental CakeML to RISC-V port; complete CakeML output parity is not yet established."

private def parseBool (text : String) : Option Bool :=
  if text == "true" then some true else if text == "false" then some false else none

private def parseArgs : List String → Options → Except String Options
  | [], options => .ok options
  | arg :: args, options =>
      if arg == "--target=riscv" then parseArgs args options
      else if arg.startsWith "--exclude_prelude=" then
        match parseBool (arg.drop "--exclude_prelude=".length |>.toString) with
        | some b => parseArgs args { options with excludePrelude := b }
        | none => .error s!"invalid Boolean option: {arg}"
      else if arg.startsWith "--skip_type_inference=" then
        match parseBool (arg.drop "--skip_type_inference=".length |>.toString) with
        | some b => parseArgs args { options with skipTypeInference := b }
        | none => .error s!"invalid Boolean option: {arg}"
      else .error s!"unsupported option: {arg}"

private def errorMessage : PrimitiveCheckedSourceResult → Option String
  | .parseExhausted => some "parser or lexer exhausted its execution bound"
  | .parseRejected => some "parsing failed"
  | .inferenceError e => some s!"type inference failed: {repr e}"
  | .backendRejected => some "compiler backend could not compile this program"
  | .success _ _ _ => none

/-- Run the currently supported CakeML frontend and backend options. This is
Flapjack CLI infrastructure, not a port of the full HOL compiler driver. -/
def compileBytes (options : Options) (source : List HolChar) : PrimitiveCheckedSourceResult := Id.run do
  let config := RiscVConfig.riscvBackendConfigExecutable
  let fuel := 10000
  match Flapjack.CakeParser.Frontend.parseSourceFuel fuel fuel source with
  | .exhausted => return .parseExhausted
  | .rejected => return .parseRejected
  | .success decls =>
    let full := if options.excludePrelude then decls else Flapjack.Basis.BasisProg.basis ++ decls
    if !options.skipTypeInference then
      match Flapjack.Compiler.Inference.Infer.Core.inferProgramFuel fuel fuel full with
      | .error e => return .inferenceError e
      | .ok _ => pure ()
    match compileCakeToRiscVConfiguredFuel fuel config full with
    | none => return .backendRejected
    | some (bytes, bitmaps, config) => return .success bytes bitmaps config

def main (args : List String) : IO UInt32 := do
  if args == ["--help"] || args == ["-h"] then
    IO.println usage
    return 0
  match parseArgs args {} with
  | .error message =>
    IO.eprintln s!"cake: {message}\n{usage}"
    return 2
  | .ok options =>
    let input ← (← IO.getStdin).readBinToEnd
    let chars := input.data.toList.map (fun c => BitVec.ofNat 8 c.toNat)
    let result := compileBytes options chars
    if let .inferenceError error := result then
      if let some bytes := Flapjack.Compiler.Inference.Infer.Diagnostics.renderUndefinedVariable chars error then
        let stderr ← IO.getStderr
        stderr.write (ByteArray.mk (bytes.map (fun b => UInt8.ofNat b.toNat)).toArray)
        return 1
    if let some message := errorMessage result then
      IO.eprintln s!"cake: {message}"
      return 1
    match result with
    | .success bytes bitmaps config =>
      IO.print (Flapjack.RiscV.CakeArtifactFormat.assembly bytes bitmaps config)
      return 0
    | _ => return 1

end Flapjack.CakeMain

def main (args : List String) : IO UInt32 := Flapjack.CakeMain.main args
