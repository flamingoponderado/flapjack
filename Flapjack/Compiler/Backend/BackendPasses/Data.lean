import Flapjack.Compiler.Backend.BackendPasses.Bvi
import Flapjack.Compiler.Backend.PresLang.Data
import Flapjack.Compiler.Backend.BviToData.Compile

/-! Capture BVI-to-data and the three following data optimizations from
`backend_passesScript.sml`. Display correspondence and executable explorer
wiring remain open; the initial lowering uses explicit fuel. -/
namespace Flapjack.Compiler.Backend.BackendPasses
open Flapjack.Basis.Pure.MlString

/-- The original four DataLang snapshots and their shared label names. -/
structure DataStages where
  raw : List (Nat × Nat × DataLang.Prog)
  live : List (Nat × Nat × DataLang.Prog)
  simplified : List (Nat × Nat × DataLang.Prog)
  spaced : List (Nat × Nat × DataLang.Prog)
  names : Spt MlString

/-- Lower the final BVI code and preserve each intermediate optimization. -/
def captureData (fuel : Nat) (bvi : BviStages) : Option DataStages := do
  let raw ← bvi.inlineBvi.mapM fun (n, arity, body) => do
    let (p, _, _) ← BviToData.compileFuel fuel arity (List.range arity) true [] body
    pure (n, arity, p)
  let live := raw.map fun (n, arity, p) => (n, arity, (DataLive.compile p .ln).1)
  let simplified := live.map fun (n, arity, p) => (n, arity, DataSimp.simp p .skip)
  let spaced := simplified.map fun (n, arity, p) => (n, arity, DataSpace.compile p)
  pure ⟨raw, live, simplified, spaced, bvi.bviNames⟩

/-- A captured raw function is transformed by the same optimization
sequence as the normal BVI-to-data entry point. -/
theorem captureData_function_result (fuel arity : Nat) (body : Bvi.Exp)
    (p : DataLang.Prog) (result next : Nat)
    (h : BviToData.compileFuel fuel arity (List.range arity) true [] body = some (p, result, next)) :
    BviToData.compileExpFuel fuel arity body =
      some (DataSpace.compile (DataSimp.simp (DataLive.compile p .ln).1 .skip)) := by
  simp [BviToData.compileExpFuel, BviToData.optimise, h]

private def title (s : String) : List HolChar := (ofString ("# " ++ s ++ "\n\n")).explode

/-- Render the four DataLang stages with the original headings. -/
def dataReportBytes (s : DataStages) : List HolChar :=
  title "after bvi_to_data" ++ PresLang.Data.functionBytes s.names s.raw ++
  title "after data_live" ++ PresLang.Data.functionBytes s.names s.live ++
  title "after data_simp" ++ PresLang.Data.functionBytes s.names s.simplified ++
  title "after data_space" ++ PresLang.Data.functionBytes s.names s.spaced

end Flapjack.Compiler.Backend.BackendPasses
