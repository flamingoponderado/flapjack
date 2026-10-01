import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.Compiler.Backend.WordAlloc.ProductionLimitVar
import Lean

/-! Standalone compiled routing-cost audit. The measured programs are actual
source frontend functions at the production pre-SSA boundary. Every input and
codec failure is reported; this does not change the compiler or claim a
performance exception or source-image theorem. -/
namespace Flapjack.LimitVarBench
open Lean Flapjack

private def frontend (source : String) : Except String (List (Nat × Nat × WordProg (RiscV.Word 64))) := do
  let parsed ← (Parser.parseTopDecs (fun value : Int => BitVec.ofInt 64 value) source).mapError reprStr
  let checked := staticCheck parsed
  let _ ← checked.1.mapError reprStr
  let declarations := panTargetMoveStartToFront "main" (panTargetDeclarationsWithDefaultMain parsed)
  let structured := structCompileTop (panSimpDecls declarations)
  let some _ := pipelineFindFunction "main" structured | throw "main entry missing"
  let globals := globalCompileTopCake structured "main"
  let crepe := crepSimpFunctions (fun value => BitVec.ofNat 64 value)
    (compileProgTopHOLWithMetadata globals)
  let loops := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel crepe
  pure (panToWordCompileProg loops)

private def prepare (body : WordProg (RiscV.Word 64)) : WordProg (RiscV.Word 64) :=
  wordBeforeSsaAllocatorBody body

@[noinline] private def direct (program : WordProg (RiscV.Word 64)) : Option Nat :=
  some (wordSsaLimitVar [] program)

@[noinline] private def native (program : WordProg (RiscV.Word 64)) : Option Nat :=
  (wordLangProgToHOL program).map Compiler.Backend.WordAlloc.limitVar

private def time (compute : WordProg (RiscV.Word 64) → Option Nat)
    (programs : Array (WordProg (RiscV.Word 64))) (repeats : Nat) : IO (Nat × Nat) := do
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [:repeats] do
    for program in programs do
      checksum := checksum + (compute program).getD 0
  let finish ← IO.monoNanosNow
  pure (finish - start, checksum)

private def run (path : String) (repeats samples : Nat) : IO Bool := do
  let source ← IO.FS.readFile path
  let some entries := (frontend source).toOption | do
    IO.eprintln s!"limit-var benchmark frontend failed: {path}: {repr (frontend source)}"
    return false
  let programs := (entries.map (fun (_, _, body) => prepare body)).toArray
  let mut rejected : Array Nat := #[]
  let mut mismatched : Array Nat := #[]
  let mut index := 0
  for program in programs do
    match native program with
    | none => rejected := rejected.push index
    | some value => if direct program != some value then mismatched := mismatched.push index
    index := index + 1
  IO.println (Json.mkObj [("kind", toJson "coverage"), ("path", toJson path),
    ("functions", toJson programs.size), ("codecRejectedIndices", toJson rejected),
    ("mismatchedIndices", toJson mismatched), ("repeats", toJson repeats)]).compress
  -- Warm both paths and observe their checksums before starting samples.
  let (_, warmDirect) ← time direct programs 1
  let (_, warmNative) ← time native programs 1
  for sample in [:samples] do
    -- Alternate order to expose ordering effects; no native projection is cached.
    let (first, second) := if sample % 2 = 0 then (direct, native) else (native, direct)
    let a ← time first programs repeats
    let b ← time second programs repeats
    let (d, n) := if sample % 2 = 0 then (a, b) else (b, a)
    IO.println (Json.mkObj [("kind", toJson "sample"), ("path", toJson path),
      ("sample", toJson sample), ("directNs", toJson d.1), ("nativeNs", toJson n.1),
      ("directChecksum", toJson d.2), ("nativeChecksum", toJson n.2),
      ("warmDirect", toJson warmDirect), ("warmNative", toJson warmNative)]).compress
  pure (rejected.isEmpty && mismatched.isEmpty)

end Flapjack.LimitVarBench

-- Deliberately separate executable: no production compiler option or route change.
def main (paths : List String) : IO UInt32 := do
  if paths.isEmpty then
    IO.eprintln "usage: flapjack-limit-var-bench SOURCE.pnk ..."
    return 2
  let repeats := ((← IO.getEnv "LIMIT_BENCH_REPEATS").getD "20").toNat?.getD 20
  let samples := ((← IO.getEnv "LIMIT_BENCH_SAMPLES").getD "5").toNat?.getD 5
  if repeats == 0 || samples == 0 then return 2
  let mut good := true
  for path in paths do
    good := (← Flapjack.LimitVarBench.run path repeats samples) && good
  return if good then 0 else 1
