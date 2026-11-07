import Flapjack.Compiler.Backend.BackendPasses.Closure
import Flapjack.Compiler.Backend.PresLang.Bvi
import Flapjack.Compiler.Backend.SourceToFlat.ToBvi
import Flapjack.Compiler.Backend.DataToWord.Names
import Flapjack.Compiler.Backend.WordToStack.StubNames
import Flapjack.Compiler.Backend.StackAlloc.StubNames
import Flapjack.Compiler.Backend.StackRemove.StubNames

/-! Capture BVL optimization and BVI stages from `backend_passesScript.sml`.
The original list snapshots precede the later DataLang and machine stages.
The checked passes use explicit fuel, and their display representations and
cross-language correspondence remain under review. -/
namespace Flapjack.Compiler.Backend.BackendPasses
open Flapjack.Basis.Pure.MlString

/-- The original BVL and BVI snapshots together with final configuration. -/
structure BviStages where
  inlineBvl : List (Nat × Nat × Bvl.Exp)
  letOpBvl : List (Nat × Nat × Bvl.Exp)
  handledBvl : List (Nat × Nat × Bvl.Exp)
  rawBvi : List (Nat × Nat × Bvi.Exp)
  tailrecBvi : List (Nat × Nat × Bvi.Exp)
  tmcBvi : List (Nat × Nat × Bvi.Exp)
  inlineBvi : List (Nat × Nat × Bvi.Exp)
  bvlNames : Spt MlString
  productionNames : Spt MlString
  bviNames : Spt MlString
  closureConfig : ClosToBvl.Config
  bvlConfig : BvlToBvi.Config

/-- Apply the original ordered pass sequence and retain every snapshot.
The input closure stage contains pre-sort code, so sorting is performed here
exactly where the normal compiler performs it. -/
def captureBvi (fuel : Nat) (c : BvlToBvi.Config) (closure : ClosureStages) : Option BviStages := do
  let sorted := ClosToBvl.codeSort closure.bvl
  let (inlines, inlined) ← BvlInline.tickInlineAllFuel fuel c.inlineSizeLimit .ln sorted
  let inlined ← inlined.mapM fun (n, arity, body) => do
    pure (n, arity, ← BvlInline.removeTicksFuel fuel body)
  let letOp ← inlined.mapM fun (n, arity, body) => do
    pure (n, arity, ← BvlInline.letOpFuel fuel body)
  let handled ← letOp.mapM fun (n, arity, body) => do
    pure (n, arity, ← BvlHandle.compileAnyFuel fuel c.splitMainAtSeq c.expCut arity body)
  let (start, raw, next1) ← BvlToBvi.compileProgFuel fuel fuel closure.config.start 0 handled
  let (next2, tailrec) ← BviTailrec.compileProgFuel fuel c.doTailrec (Flapjack.bvlNumStubs + 2) raw
  let (next3, tmc) ← BviTmc.compileProgFuel fuel c.doTmc (Flapjack.bvlNumStubs + 3) tailrec
  let (bviInlines, inlineBvi) ← BviInline.compileProgFuel fuel tmc
  let productionNames := BvlToBvi.getNames (inlineBvi.map (fun (n, _, _) => n)) closure.names
  let stubs := DataToWord.stubNames () ++ WordToStack.stubNames () ++
    StackAlloc.stubNames () ++ StackRemove.stubNames ()
  let names := sptUnion (sptFromAList stubs) productionNames
  let closureConfig := { closure.config with start := start }
  let bvlConfig := { c with inlines := inlines, bviInlines := bviInlines, nextName1 := next1, nextName2 := next2, nextName3 := next3 }
  pure ⟨inlined, letOp, handled, raw, tailrec, tmc, inlineBvi, closure.names, productionNames, names, closureConfig, bvlConfig⟩

private def title (s : String) : List HolChar := (ofString ("# " ++ s ++ "\n\n")).explode

/-- Render the seven snapshots using the original stage names and name maps. -/
def bviReportBytes (s : BviStages) : List HolChar :=
  title "after bvl_inline and remove_ticks" ++ PresLang.Bvl.programBytes s.bvlNames s.inlineBvl ++
  title "after let_op_sing" ++ PresLang.Bvl.programBytes s.bvlNames s.letOpBvl ++
  title "after bvl_handle" ++ PresLang.Bvl.programBytes s.bvlNames s.handledBvl ++
  title "after bvl_to_bvi" ++ PresLang.Bvi.programBytes s.bviNames s.rawBvi ++
  title "after bvi_tailrec" ++ PresLang.Bvi.programBytes s.bviNames s.tailrecBvi ++
  title "after bvi_tmc" ++ PresLang.Bvi.programBytes s.bviNames s.tmcBvi ++
  title "after bvi_inline" ++ PresLang.Bvi.programBytes s.bviNames s.inlineBvi

end Flapjack.Compiler.Backend.BackendPasses
