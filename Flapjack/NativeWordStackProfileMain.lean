import Flapjack.Pancake.PanToTarget.ProductionSourceEntry
import Flapjack.Compiler.Backend.WordToWord.ExecutableCompile
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import Flapjack.Parser.ParseTopDecsByteRanged

/-! Optional compiled phase profiler for native route adoption. This is a
measurement tool, not compiler routing or a HOL theorem. It splits the exact
native pipeline used by the whole-backend experiment at existing pass boundaries.
IO/noinline barriers and immediate stderr flushing identify an unfinished phase.
Complete native output bytes are saved for independent original-output comparison;
timings or matching byte counts alone are not correctness evidence. -/

namespace Flapjack.NativeWordStackProfile
open Flapjack.Compiler.Backend Flapjack.Pancake.PanLang

abbrev WordRows := List (Nat × Nat × WordLangProgHOL (BitVec 64))
abbrev StackResult := List (BitVec 64) × WordToStack.Native.Config × List Nat ×
  List (Nat × StackLang.HolProg 64)

@[noinline] def sourcePhase (source : String) : IO (Option WordRows) := do
  match parsed : Parser.parseTopDecs (fun n => BitVec.ofInt 64 n) source with
  | .error _ => return none
  | .ok declarations =>
    let ranged := Parser.parseTopDecs_declByteRanged _ source false declarations parsed
    return Pancake.PanToTarget.compileSourceWordNative? declarations ranged

@[noinline] def wordPhase (rows : WordRows) : IO WordRows := do
  return (WordToWord.compileExecutable RiscVConfig.pancakeRiscVBackendConfig.wordToWordConf
    Compiler.Encoders.RiscV.Target.riscvConfig rows).2

@[noinline] def stackPhase (rows : WordRows) : IO StackResult := do
  return WordToStack.Native.compileNative Compiler.Encoders.RiscV.Target.riscvConfig
    RiscVConfig.pancakeRiscVBackendConfig.stackConf.perfCalls rows

@[noinline] def lowerPhase (result : StackResult) :
    IO (Option (List (BitVec 8) × List (BitVec 64) × Backend.Config)) := do
  let (bitmaps, wordConf, _frames, rows) := result
  return Backend.fromStack Compiler.Encoders.RiscV.Target.riscvConfig
    { RiscVConfig.pancakeRiscVBackendConfig with wordConf := wordConf } .ln rows bitmaps

def report (path phase : String) (detail : String := "") : IO Unit := do
  let stream ← IO.getStderr
  stream.putStrLn s!"native-phase path={path} phase={phase} {detail}"
  stream.flush

def profile (outputDir : System.FilePath) (index : Nat) (path : String) : IO Bool := do
  let source ← IO.FS.readFile path
  report path "source.start"
  let start ← IO.monoMsNow
  let some input ← sourcePhase source | report path "source.reject"; return false
  let prefixEnd ← IO.monoMsNow
  report path "source.end" s!"ms={prefixEnd-start} rows={input.length}"
  report path "word.start"
  let wordStart ← IO.monoMsNow
  let word ← wordPhase input
  let wordEnd ← IO.monoMsNow
  report path "word.end" s!"ms={wordEnd-wordStart} rows={word.length}"
  report path "stack.start"
  let stackStart ← IO.monoMsNow
  let stack ← stackPhase word
  let stackEnd ← IO.monoMsNow
  report path "stack.end"
    s!"ms={stackEnd-stackStart} rows={stack.2.2.2.length} frames={stack.2.2.1.length} bitmaps={stack.1.length} bitmapCount={stack.2.1.bitmapsLength}"
  report path "lower.start"
  let lowerStart ← IO.monoMsNow
  let some (bytes, bitmaps, _config) ← lowerPhase stack |
    report path "lower.reject"; return false
  let finish ← IO.monoMsNow
  let output := outputDir / s!"{index}.bin"
  IO.FS.writeBinFile output (ByteArray.mk (bytes.map (fun b => b.toNat.toUInt8)).toArray)
  report path "lower.end"
    s!"ms={finish-lowerStart} totalMs={finish-start} bytes={bytes.length} bitmaps={bitmaps.length} artifact={output}"
  return true

def main (args : List String) : IO UInt32 := do
  let outputDir :: paths := args |
    IO.eprintln "usage: flapjack-native-wordstack-profile OUTPUT_DIR SOURCE..."; return 2
  if paths.isEmpty then
    IO.eprintln "at least one source path is required"
    return 2
  IO.FS.createDirAll outputDir
  let mut failures := 0
  for (path, index) in paths.zipIdx do
    if !(← profile outputDir index path) then failures := failures + 1
  return if failures = 0 then 0 else 1

end Flapjack.NativeWordStackProfile

def main := Flapjack.NativeWordStackProfile.main
