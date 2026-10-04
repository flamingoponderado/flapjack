import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.RiscV.ArtifactFormat
import Flapjack.RiscV.NativeCLIAdapter

/-!
# Flapjack compiler command

This command-line wrapper exposes the checked source-facing RV64I pipeline as
a Pancake-compatible assembly frame, raw bytes, or linked sections.  Assembly
is the default and `--assembly` is retained as a compatibility alias for
`--pancake`; code and layout differences remain tracked by the parity beads.
-/

namespace Flapjack

def compileRemoveConfig : StackRemoveConfig :=
  { storeBase := 10
    currHeap := 12
    scratch := 31
    addressScratch := 29
    stackPointer := 24
    bytesInWord := 8
    stackBase := 25
    wordShift := 3
    jump := false }

open RiscV.NativeCLI (hexBytes)

inductive OutputFormat where
  | pancake
  | hex
  | sections
  deriving DecidableEq

def usage : String :=
  "Usage: lake exe flapjack-compile [--assembly|--pancake|--hex|--sections] " ++
  "[SOURCE.pnk]\nRead Pancake source from SOURCE.pnk or stdin. The default, " ++
  "--assembly, and --pancake modes emit the Pancake-compatible assembly " ++
  "frame; --hex emits that frame's code bytes as one lowercase line; " ++
  "--sections emits its sections as <label> <address> <bytes> lines."

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

def printSections (sections : List (RiscV.EncodedRiscVSection width)) : IO Unit := do
  for entry in sections do
    IO.println (s!"{entry.label} {entry.address.toNat} " ++ hexBytes entry.bytes)

/-- The parser-backed native whole compiler (`RiscV.NativeSource.compile`), rendered from its
whole tuple by `RiscV.NativeCLI`. Opt-in with a leading `--native` until its corpus parity
and performance are established. -/
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

def compileMain (arguments : List String) : IO UInt32 := do
  if arguments.head? == some "--native" then
    let some (outputFormat, path) ← parseArguments arguments.tail | return 0
    return ← compileMainNative outputFormat path
  let some (outputFormat, path) ← parseArguments arguments | return 0
  let source ← readSource path
  if outputFormat == .pancake then
    match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64) .rv64i
        riscv64BytesInWord (BitVec.ofInt 64) [] compileRemoveConfig
        "main" source with
    | .ok image =>
        for warning in image.warnings do
          IO.eprintln s!"warning: {repr warning}"
        IO.print (RiscV.pancakeRuntimeAssembly image.crepe image)
        return 0
    | .error error =>
        IO.eprintln s!"flapjack-compile: {sourceRiscVImageErrorDescription error}"
        return 1
  else
    -- `--sections` and `--hex` render the same native runtime image as the
    -- assembly frame: its sections, or its concatenated code bytes.
    match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64) .rv64i
        riscv64BytesInWord (BitVec.ofInt 64) [] compileRemoveConfig
        "main" source with
    | .ok image =>
        for warning in image.warnings do
          IO.eprintln s!"warning: {repr warning}"
        if outputFormat == .sections then
          printSections image.sections
        else
          IO.println (hexBytes (image.sections.flatMap (fun entry => entry.bytes)))
        return 0
    | .error error =>
        IO.eprintln s!"flapjack-compile: {sourceRiscVImageErrorDescription error}"
        return 1

end Flapjack

def main (arguments : List String) : IO UInt32 := Flapjack.compileMain arguments
