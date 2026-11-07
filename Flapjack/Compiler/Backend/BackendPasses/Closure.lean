import Flapjack.Compiler.Backend.BackendPasses.Frontend
import Flapjack.Compiler.Backend.PresLang.Bvl
import Flapjack.Compiler.Backend.ClosToBvl.Prepared

/-! Capture the closure and BVL stages from `backend_passesScript.sml`.
The bounded optimizers can report exhaustion. Display carriers and complete
cross-language correspondence remain under review; subsequent stages and
the explorer driver are not yet connected. -/
namespace Flapjack.Compiler.Backend.BackendPasses
open Flapjack.Basis.Pure.MlString

/-- Snapshot the original closure optimizations and pre-sort BVL output. -/
structure ClosureStages where
  mti : List ClosLang.Exp
  numbered : List ClosLang.Exp
  known : List ClosLang.Exp
  called : List ClosLang.Exp
  auxiliary : List (Nat × Nat × ClosLang.Exp)
  annotated : List (Nat × Nat × ClosLang.Exp)
  bvl : List (Nat × Nat × Bvl.Exp)
  names : Spt MlString
  config : ClosToBvl.Config

/-- Capture the same closure pass order as CakeML, retaining the unsorted
BVL stage shown by the explorer. `none` denotes a bounded pass failure. -/
def captureClosure (fuel : Nat) (c : ClosToBvl.Config) (es : List ClosLang.Exp) : Option ClosureStages := do
  let mti ← ClosMti.compileFuel fuel c.doMti c.maxApp es
  let loc := c.nextLoc + max 1 mti.length
  let loc := if loc % 2 = 0 then loc else loc + 1
  let (next, numbered) := ClosNumber.renumberList loc mti
  let (knownConfig, known) ← ClosKnown.compileFuel fuel c.knownConf numbered
  let (called, callState) ← ClosCall.compileFuel fuel c.doCall known
  let annotated := ClosAnnotate.compile (ClosToBvl.chainExps c.nextLoc called ++ callState.2)
  let current := { c with start := c.nextLoc, nextLoc := next, knownConf := knownConfig, callState := callState }
  let n := ClosToBvl.numStubs current.maxApp
  let initial := (sptToAList (ClosToBvl.initCode current.maxApp)).map fun (loc, arity, code) => (loc, arity, code)
  let compiled ← ClosToBvl.compileProg? current.maxApp annotated
  let bvl := initial ++ [(n - 2, 2, ClosToBvl.forceThunkCode),
    (n - 1, 0, ClosToBvl.initGlobals current.maxApp (n + current.start))] ++ compiled
  let names := ClosToBvl.makeNameAlist (bvl.map (fun (loc, _, _) => loc)) annotated n c.nextLoc es.length
  pure ⟨mti, numbered, known, called, callState.2, annotated, bvl, names, { current with start := n - 1 }⟩

/-- On success, the captured BVL program sorts to the production result. -/
theorem captureClosure_result (fuel : Nat) (c : ClosToBvl.Config) (es : List ClosLang.Exp)
    (stages : ClosureStages) (h : captureClosure fuel c es = some stages) :
    ClosToBvl.compileCallMtiFuel? fuel c es =
      some (stages.config, ClosToBvl.codeSort stages.bvl, stages.names) := by
  simp only [captureClosure, Option.bind_eq_bind, Option.bind] at h
  simp only [ClosToBvl.compileCallMtiFuel?, ClosToBvl.compilePrepared?, Option.bind_eq_bind, Option.bind]
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  cases h
  simp

private def title (s : String) : List HolChar := (ofString ("# " ++ s ++ "\n\n")).explode
private def bytes (fragments : List String) : List HolChar :=
  fragments.flatMap fun fragment => fragment.toList.map (fun c => BitVec.ofNat 8 c.toNat)

/-- Render the captured closure stages and unsorted BVL stage. -/
def closureReportBytes (stages : ClosureStages) : List HolChar :=
  title "after clos_mti" ++ bytes (PresLang.Clos.sourcePrograms stages.mti []) ++
  title "after clos_number" ++ bytes (PresLang.Clos.sourcePrograms stages.numbered []) ++
  title "after clos_known" ++ bytes (PresLang.Clos.sourcePrograms stages.known []) ++
  title "after clos_call" ++ bytes (PresLang.Clos.sourcePrograms stages.called stages.auxiliary) ++
  title "after clos_annotate" ++ bytes (PresLang.Clos.sourcePrograms [] stages.annotated) ++
  title "after clos_to_bvl" ++ PresLang.Bvl.programBytes stages.names stages.bvl

end Flapjack.Compiler.Backend.BackendPasses
