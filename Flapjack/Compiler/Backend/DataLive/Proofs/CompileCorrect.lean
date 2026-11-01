import Flapjack.Compiler.Backend.DataLive.Proofs.CompileAll

/-! Observable consequences of the data liveness simulation. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- A state has the required exception correspondence with itself. -/
theorem exceptionRel_refl {C F : Type} (state : State C F) : exceptionRel state state := by
  intro jumped run
  exact ⟨jumped, run, stateRel_refl jumped .ln, rfl, rfl⟩

/-- Starting from the same state, compiled data code has the same
non-type-error result and related final state. This auxiliary theorem is not
tagged as the original stronger HOL `compile_correct`. -/
theorem compile_sameResult {C F : Type} (program : DataLang.Prog) (live : NumSet)
    (source sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (run : DataSem.evaluate program source = (result, sourceNext))
    (notType : result ≠ some (.err (.abort .typeError))) :
    ∃ targetNext, DataSem.evaluate (compile program live).1 source = (result, targetNext) ∧
      stateRel sourceNext targetNext (postLive result live) := by
  exact simulationFor_all program live source source result sourceNext run
    (stateRel_refl source _) notType (exceptionRel_refl source)

/-- A raised result of liveness-compiled code has the original state except
for the four fields explicitly permitted by the source correctness theorem.
This is the raise case only; source-carrier review remains open. -/
theorem compile_correct_raise {C F : Type} (program : DataLang.Prog) (source sourceNext : State C F)
    (value : DataSem.Value)
    (run : DataSem.evaluate program source = (some (.err (.raise value)), sourceNext)) :
    ∃ localsSize stackMax safe peak,
      DataSem.evaluate (compile program .ln).1 source =
        (some (.err (.raise value)), { sourceNext with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }) := by
  obtain ⟨targetNext, targetRun, related⟩ :=
    compile_sameResult program .ln source sourceNext (some (.err (.raise value))) run (by simp)
  have sourceControl := evaluate_stackResult program source sourceNext (some (.err (.raise value))) run
  have targetControl := evaluate_stackResult (compile program .ln).1 source targetNext (some (.err (.raise value))) targetRun
  obtain ⟨sourceJump, sourceJumpRun, sourceStack, sourceHandler, sourceLocals⟩ := sourceControl
  obtain ⟨targetJump, targetJumpRun, targetStack, targetHandler, targetLocals⟩ := targetControl
  have jumpEq : sourceJump = targetJump := Option.some.inj (sourceJumpRun.symm.trans targetJumpRun)
  subst targetJump
  have stackEq : sourceNext.stack = targetNext.stack := sourceStack.trans targetStack.symm
  have handlerEq : sourceNext.handler = targetNext.handler := sourceHandler.trans targetHandler.symm
  have localsEq : sourceNext.locals = targetNext.locals := sourceLocals.trans targetLocals.symm
  have stateEq : targetNext = { sourceNext with localsSize := targetNext.localsSize, stackMax := targetNext.stackMax, safeForSpace := targetNext.safeForSpace, peakHeapLength := targetNext.peakHeapLength } := by
    rcases related with ⟨code, clock, space, ffi, refs, global, _, _, compiler, oracle, stamps, limits, frames, _⟩
    cases sourceNext
    cases targetNext
    simp_all
  refine ⟨targetNext.localsSize, targetNext.stackMax, targetNext.safeForSpace, targetNext.peakHeapLength, ?_⟩
  rw [← stateEq]
  exact targetRun

end Flapjack.Compiler.Backend.DataLive
