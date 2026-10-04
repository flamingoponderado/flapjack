import Lean
import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.Compiler.Backend.WordCse.ProductionProgram
import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAMetadata
open Flapjack Flapjack.RiscV Flapjack.Compiler.Backend.WordCse
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Force traversal of every nested program, including both Call continuations.
Timing excludes the complete rendering comparison below. -/
def programNodes : WordProg (BitVec 64) → Nat
  | .seq a b | .ite _ _ _ a b => 1 + programNodes a + programNodes b
  | .loop _ b _ | .mustTerminate b => 1 + programNodes b
  | .call returns _ _ handler =>
    1 + (match returns with | none => 0 | some (_, _, body, _, _) => programNodes body) +
      (match handler with | none => 0 | some (_, body, _, _) => programNodes body)
  | _ => 1
termination_by p => sizeOf p
/-- IO call boundary prevents pure computation from moving across the clocks. -/
@[noinline] def runNative (input : WordLangProgHOL (BitVec 64)) : IO (Nat × WordProg (BitVec 64) × Knowledge) := do
  let (knowledge, transformed) := wordCse emptyData input
  let some output := wordLangProgFromHOL transformed |
    throw (IO.userError "CSE output decoder rejection")
  return (programNodes output, output, knowledge)
@[noinline] def runActual (input : WordProg (BitVec 64)) : IO (Nat × WordProg (BitVec 64) × WordCseKnowledge) := do
  let (output, knowledge) := wordCseProg wordCseEmpty input
  return (programNodes output, output, knowledge)
def factEntries : Misc.BalancedMap.Map (List Nat) Nat → List (List Nat × Nat)
  | .tip => []
  | .bin _ key value left right => factEntries left ++ [(key, value)] ++ factEntries right

def sameKnowledge (native : Knowledge) (actual : WordCseKnowledge) : Bool :=
  let sorted (entries : List (Nat × Nat)) := entries.mergeSort (fun a b => a.1 ≤ b.1)
  sorted (sptToAList native.toCanonical) == actual.toCanonical.toList &&
    sorted (sptToAList native.toLatest) == actual.toLatest.toList &&
    sorted (native.getsMem.map (fun (store, register) =>
      (wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec 64)), register))) == actual.getsMem.toList &&
    factEntries native.instrsMem == actual.instrsMem.toList &&
    factEntries native.loadsMem == actual.loadsMem.toList

def profileBody (path : String) (label arity : Nat) (body : WordProg (BitVec 64)) : IO Unit := do
  let selected := wordInstSelectProgramFrom (wordFuseConditionsAndFold (wordConstFp (wordFlattenProgramFrom body)))
  let some encoded := wordLangProgToHOL selected | throw (IO.userError "selected encoder rejection")
  let some (_, _, ssa) := wordFullSsaCcTransNativeWithStateFromHOL arity encoded | throw (IO.userError "SSA output rejection")
  let input := wordRemoveDeadProgramViaHOL ssa
  let some native := wordLangProgToHOL input | throw (IO.userError "CSE input encoder rejection")
  let some canonical := wordLangProgFromHOL native | throw (IO.userError "CSE input decoder rejection")
  if reprStr canonical != reprStr input then throw (IO.userError "CSE input roundtrip changed actual representation")
  let begin ← IO.monoNanosNow
  let (nativeSize, expected, nativeKnowledge) ← runNative native
  let middle ← IO.monoNanosNow
  let (actualSize, actual, actualKnowledge) ← runActual input
  let finish ← IO.monoNanosNow
  if nativeSize != actualSize then throw (IO.userError "complete structural size mismatch")
  if reprStr expected != reprStr actual then throw (IO.userError "full actual/native CSE output differs")
  if !sameKnowledge nativeKnowledge actualKnowledge then throw (IO.userError "complete five-field knowledge differs")
  IO.println s!"file={path} label={label} native_decode_ns={middle-begin} actual_ns={finish-middle} size={actualSize} exact=true knowledge_exact=true"
def profileSource (path : String) : IO Unit := do
  let source ← IO.FS.readFile path
  match hparse : Parser.parseTopDecs (BitVec.ofInt 64) source with
  | .error _ => throw (IO.userError "parse failure")
  | .ok declarations =>
    let ranged := Parser.parseTopDecs_declByteRanged (BitVec.ofInt 64) source false declarations hparse
    let targetRanged := panTargetDeclarationsWithDefaultMain_byteRanged declarations ranged
    let some pipeline := compileFlapjackEntryCake .rv64i (BitVec.ofNat 64 8) (fun n => BitVec.ofNat 64 n) "main" (panTargetDeclarationsWithDefaultMain declarations) (some (.isTrue targetRanged)) | throw (IO.userError "entry failure")
    let entries := panToWordCompileProg (pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel pipeline.crepe)
    for (label, arity, body) in entries do profileBody path label arity body

def profileCorpus : IO Unit := do
  let raw ← IO.FS.readFile "scripts/parity-small-corpus.json"
  let .ok json := Lean.Json.parse raw | throw (IO.userError "invalid corpus JSON")
  let .ok fixtures := json.getObjValAs? (Array Lean.Json) "fixtures" | throw (IO.userError "missing fixtures")
  for fixture in fixtures do
    let .ok path := fixture.getObjValAs? String "path" | throw (IO.userError "missing path")
    profileSource path
  IO.println s!"sources={fixtures.size} complete=true"
#eval profileCorpus
