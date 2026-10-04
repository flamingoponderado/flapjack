import Lean
import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.Compiler.Backend.WordSimp.ProductionSmartSeq

open Flapjack Flapjack.RiscV Flapjack.Compiler.Backend.WordSimp
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def smartSeqProgramNodes : WordProg (BitVec 64) → Nat
  | .seq a b | .ite _ _ _ a b => 1 + smartSeqProgramNodes a + smartSeqProgramNodes b
  | .loop _ b _ | .mustTerminate b => 1 + smartSeqProgramNodes b
  | .call returns _ _ handler =>
      1 + (match returns with | none => 0 | some (_, _, body, _, _) => smartSeqProgramNodes body) +
        (match handler with | none => 0 | some (_, body, _, _) => smartSeqProgramNodes body)
  | _ => 1
termination_by p => sizeOf p

/-- A literal full-codec route to the reviewed native SmartSeq, without output
fallback. Rejecting an input or output fails the measurement. -/
def nativeSmartSeqCodec (first second : WordProg (BitVec 64)) :
    IO (WordProg (BitVec 64)) := do
  let some a := wordLangProgToHOL first | throw (IO.userError "first encoder rejection")
  let some b := wordLangProgToHOL second | throw (IO.userError "second encoder rejection")
  let some output := wordLangProgFromHOL (smartSeqHOL a b) |
    throw (IO.userError "SmartSeq output decoder rejection")
  return output

-- IO boundaries keep the pure actual computation between monotonic clocks.
@[noinline] def smartSeqRunNative (statements : List (WordProg (BitVec 64))) :
    IO (Nat × WordProg (BitVec 64)) := do
  let output ← statements.foldlM nativeSmartSeqCodec .skip
  return (smartSeqProgramNodes output, output)

@[noinline] def smartSeqRunActual (statements : List (WordProg (BitVec 64))) :
    IO (Nat × WordProg (BitVec 64)) := do
  let output := wordSimpLeftSeq statements
  return (smartSeqProgramNodes output, output)

def smartSeqProfileBody (path : String) (label : Nat) (body : WordProg (BitVec 64)) : IO Unit := do
  let statements := wordSimpSeqItems body
  let begin ← IO.monoNanosNow
  let (nativeSize, expected) ← smartSeqRunNative statements
  let middle ← IO.monoNanosNow
  let (actualSize, actual) ← smartSeqRunActual statements
  let finish ← IO.monoNanosNow
  if nativeSize != actualSize then throw (IO.userError "complete node-count mismatch")
  if reprStr expected != reprStr actual then
    throw (IO.userError s!"complete SmartSeq output mismatch: {path} label={label}")
  IO.println s!"file={path} label={label} statements={statements.length} native_codec_ns={middle-begin} actual_ns={finish-middle} size={actualSize} exact=true"

def smartSeqProfileSource (path : String) : IO Unit := do
  let source ← IO.FS.readFile path
  match hparse : Parser.parseTopDecs (BitVec.ofInt 64) source with
  | .error _ => throw (IO.userError "parse failure")
  | .ok declarations =>
      let ranged := Parser.parseTopDecs_declByteRanged (BitVec.ofInt 64) source false declarations hparse
      let targetRanged := panTargetDeclarationsWithDefaultMain_byteRanged declarations ranged
      let some pipeline := compileFlapjackEntryCake .rv64i (BitVec.ofNat 64 8)
          (fun n => BitVec.ofNat 64 n) "main" (panTargetDeclarationsWithDefaultMain declarations)
          (some (.isTrue targetRanged)) | throw (IO.userError "entry failure")
      let entries := panToWordCompileProg
        (pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel pipeline.crepe)
      for (label, _, body) in entries do smartSeqProfileBody path label body

def smartSeqProfileCorpus : IO Unit := do
  let raw ← IO.FS.readFile "scripts/parity-small-corpus.json"
  let .ok json := Lean.Json.parse raw | throw (IO.userError "invalid corpus JSON")
  let .ok fixtures := json.getObjValAs? (Array Lean.Json) "fixtures" |
    throw (IO.userError "missing fixtures")
  for fixture in fixtures do
    let .ok path := fixture.getObjValAs? String "path" | throw (IO.userError "missing path")
    smartSeqProfileSource path
  IO.println s!"sources={fixtures.size} complete=true"

#eval smartSeqProfileCorpus
