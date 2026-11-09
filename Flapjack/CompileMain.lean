import Flapjack.RiscV.NativeCLIAdapter
import Flapjack.Mips32.NativeCLIAdapter
import Flapjack.Arm8.NativeCLIAdapter
import Flapjack.X64.NativeCLIAdapter

/-!
# Flapjack compiler command

This command-line wrapper compiles Pancake source with the parser-backed native whole
compiler `RiscV.NativeSource.compile` and renders its result as a Pancake-compatible
assembly frame, raw bytes, or linked sections. `nativeCLIOutput_correct` connects
successful output to source correctness under explicit source/main, machine,
installation and resource premises. It identifies the rendering of the compiled
tuple, not correctness of assembly rendering or startup installation. Assembly
is the default and `--assembly` is retained as a compatibility alias for `--pancake`. A
leading `--target=mips32` selects the MIPS32 (Ziren) backend, `Mips32.NativeSource.compile`, whose
successful output `mips32CLIOutput_correct` connects to source correctness in the same way.
A leading `--target=arm8` selects the ARMv8 (AArch64) backend,
`Arm8.NativeSource.compile`, whose successful output is identified by
`Arm8.NativeCLI.output_ok`.  A leading `--target=x64` selects the x86-64
backend, `X64.NativeSource.compile`, whose successful output `x64CLIOutput_correct`
connects to source correctness in the same way as the MIPS32 route (via
`X64.NativeCLI.output_ok`).  The ARMv8 target proves `encoderCorrect arm8Target`
for the closed ARMv8 model in `Flapjack/Compiler/Encoders/Arm8/Machine/` and
instantiates the Pancake-to-machine-code theorem there; that model covers the
emitted instruction subset.  The same target also proves
`arm8EncoderCorrectL3 : encoderCorrect arm8TargetL3` over the L3
`arm8_state`/`NextStateARM8` model in
`Flapjack/Compiler/Encoders/Arm8/L3/CorrectnessEncoding/Complete.lean`, and
`panToTargetCompileSemanticsArm8L3` in
`Flapjack/Pancake/Proofs/PanToTarget/Arm8L3Instance.lean` instantiates the
Pancake-to-target theorem at that L3 configuration.  Those L3 theorems are about
the logical `compile_prog_max`; the executed `--target=arm8` driver runs the
computable `arm8Config` (the encoder-only configuration in
`Arm8/Configuration.lean`, not the closed machine model), and no theorem yet
connects its output to the L3 result.
-/

namespace Flapjack

open RiscV.NativeCLI (hexBytes)

inductive OutputFormat where
  | pancake
  | hex
  | sections
  deriving DecidableEq

def usage : String :=
  "Usage: lake exe flapjack-compile [--target=riscv64|--target=mips32|--target=arm8|--target=x64] " ++
  "[--assembly|--pancake|--hex|--sections] " ++
  "[SOURCE.pnk]\nRead Pancake source from SOURCE.pnk or stdin. The default, " ++
  "--assembly, and --pancake modes emit the Pancake-compatible assembly " ++
  "frame; --hex emits that frame's code bytes as one lowercase line; " ++
  "--sections emits its sections as <label> <address> <bytes> lines. " ++
  "--target=mips32 compiles for the MIPS32 (Ziren) target; " ++
  "--target=arm8 compiles for the ARMv8 (AArch64) target; --target=x64 " ++
  "compiles for x86-64; --target=riscv64 " ++
  "is the default."

def parseArguments (arguments : List String) : IO (Option (OutputFormat × Option String)) := do
  match arguments with
  | [] =>
      pure (some (.pancake, none))
  | [argument] =>
      if argument == "--help" || argument == "-h" then
        IO.println usage
        pure none
      else if argument == "--assembly" || argument == "--pancake" then
        pure (some (.pancake, none))
      else if argument == "--hex" then
        pure (some (.hex, none))
      else if argument == "--sections" then
        pure (some (.sections, none))
      else
        pure (some (.pancake, some argument))
  | [format, argument] =>
      let outputFormat ←
        if format == "--assembly" || format == "--pancake" then pure .pancake
        else if format == "--hex" then pure .hex
        else if format == "--sections" then pure .sections
        else do
          IO.eprintln s!"flapjack-compile: unknown option {format}\n{usage}"
          IO.Process.exit 2
      pure (some (outputFormat, some argument))
  | _ =>
      IO.eprintln s!"flapjack-compile: expected at most one input path\n{usage}"
      IO.Process.exit 2

def readSource (path : Option String) : IO String := do
  match path with
  | none =>
      let stdin ← IO.getStdin
      pure (← stdin.readToEnd)
  | some argument => IO.FS.readFile argument

/-- The parser-backed native whole compiler (`RiscV.NativeSource.compile`), rendered from its
whole tuple by `RiscV.NativeCLI`. This is the default route for every output mode. -/
def compileMainNative (outputFormat : OutputFormat) (path : Option String) : IO UInt32 := do
  let source ← readSource path
  let format : RiscV.NativeCLI.Format :=
    match outputFormat with
    | .pancake => .assembly
    | .hex => .hex
    | .sections => .sections
  match RiscV.NativeCLI.output format source with
  | .error message =>
      IO.eprintln s!"flapjack-compile: {message}"
      return 1
  | .ok (warnings, text) =>
      for warning in warnings do
        IO.eprintln s!"warning: {warning}"
      IO.print text
      return 0

/-- The MIPS32 (Ziren) compiler (`Mips32.NativeSource.compile`), rendered by
`Mips32.NativeCLI`. -/
def compileMainMips32 (outputFormat : OutputFormat) (path : Option String) : IO UInt32 := do
  let source ← readSource path
  let format : RiscV.NativeCLI.Format :=
    match outputFormat with
    | .pancake => .assembly
    | .hex => .hex
    | .sections => .sections
  match Mips32.NativeCLI.output format source with
  | .error message =>
      IO.eprintln s!"flapjack-compile: {message}"
      return 1
  | .ok (warnings, text) =>
      for warning in warnings do
        IO.eprintln s!"warning: {warning}"
      IO.print text
      return 0

/-- The ARMv8 (AArch64) compiler (`Arm8.NativeSource.compile`), rendered by
`Arm8.NativeCLI`. -/
def compileMainArm8 (outputFormat : OutputFormat) (path : Option String) : IO UInt32 := do
  let source ← readSource path
  let format : RiscV.NativeCLI.Format :=
    match outputFormat with
    | .pancake => .assembly
    | .hex => .hex
    | .sections => .sections
  match Arm8.NativeCLI.output format source with
  | .error message =>
      IO.eprintln s!"flapjack-compile: {message}"
      return 1
  | .ok (warnings, text) =>
      for warning in warnings do
        IO.eprintln s!"warning: {warning}"
      IO.print text
      return 0

/-- The x86-64 compiler (`X64.NativeSource.compile`), rendered by
`X64.NativeCLI`. -/
def compileMainX64 (outputFormat : OutputFormat) (path : Option String) : IO UInt32 := do
  let source ← readSource path
  let format : RiscV.NativeCLI.Format :=
    match outputFormat with
    | .pancake => .assembly
    | .hex => .hex
    | .sections => .sections
  match X64.NativeCLI.output format source with
  | .error message =>
      IO.eprintln s!"flapjack-compile: {message}"
      return 1
  | .ok (warnings, text) =>
      for warning in warnings do
        IO.eprintln s!"warning: {warning}"
      IO.print text
      return 0

/-- The command: the native whole compiler by default (`--native` is accepted as an
explicit alias). -/
def compileMain (arguments : List String) : IO UInt32 := do
  match arguments with
  | "--native" :: rest =>
      let some (outputFormat, path) ← parseArguments rest | return 0
      compileMainNative outputFormat path
  | "--target=riscv64" :: rest =>
      let some (outputFormat, path) ← parseArguments rest | return 0
      compileMainNative outputFormat path
  | "--target=mips32" :: rest =>
      let some (outputFormat, path) ← parseArguments rest | return 0
      compileMainMips32 outputFormat path
  | "--target=arm8" :: rest =>
      let some (outputFormat, path) ← parseArguments rest | return 0
      compileMainArm8 outputFormat path
  | "--target=x64" :: rest =>
      let some (outputFormat, path) ← parseArguments rest | return 0
      compileMainX64 outputFormat path
  | _ =>
      let some (outputFormat, path) ← parseArguments arguments | return 0
      compileMainNative outputFormat path

end Flapjack

def main (arguments : List String) : IO UInt32 := Flapjack.compileMain arguments
