module

public import Flapjack.Compiler.Backend.DataLive.Proofs.CompileAll
public import Flapjack.Compiler.Backend.Semantics.DataProps.AbortControl

@[expose] public section

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

/-- A value result of liveness-compiled code has the original state except
for the four fields permitted by the source correctness theorem. This is the
value case only; source-carrier review remains open. -/
theorem compile_correct_value {C F : Type} (program : DataLang.Prog) (source sourceNext : State C F)
    (values : List DataSem.Value)
    (run : DataSem.evaluate program source = (some (.val values), sourceNext)) :
    ∃ localsSize stackMax safe peak,
      DataSem.evaluate (compile program .ln).1 source =
        (some (.val values), { sourceNext with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }) := by
  obtain ⟨targetNext, targetRun, related⟩ :=
    compile_sameResult program .ln source sourceNext (some (.val values)) run (by simp)
  have sourceControl := evaluate_stackResult program source sourceNext (some (.val values)) run
  have targetControl := evaluate_stackResult (compile program .ln).1 source targetNext (some (.val values)) targetRun
  have stackEq : sourceNext.stack = targetNext.stack := sourceControl.1.trans targetControl.1.symm
  have handlerEq : sourceNext.handler = targetNext.handler := sourceControl.2.trans targetControl.2.symm
  have localsEq : sourceNext.locals = targetNext.locals :=
    (evaluate_value_locals program source sourceNext values run).trans
      (evaluate_value_locals (compile program .ln).1 source targetNext values targetRun).symm
  have stateEq : targetNext = { sourceNext with localsSize := targetNext.localsSize, stackMax := targetNext.stackMax, safeForSpace := targetNext.safeForSpace, peakHeapLength := targetNext.peakHeapLength } := by
    rcases related with ⟨code, clock, space, ffi, refs, global, _, _, compiler, oracle, stamps, limits, frames, _⟩
    cases sourceNext
    cases targetNext
    simp_all
  refine ⟨targetNext.localsSize, targetNext.stackMax, targetNext.safeForSpace, targetNext.peakHeapLength, ?_⟩
  rw [← stateEq]
  exact targetRun

/-- A non-type-error abort has the same final state up to the four fields
permitted by the source correctness theorem. Source-carrier review remains open. -/
theorem compile_correct_abort {C F : Type} (program : DataLang.Prog) (source sourceNext : State C F)
    (reason : Abort) (notType : reason ≠ .typeError)
    (run : DataSem.evaluate program source = (some (.err (.abort reason)), sourceNext)) :
    ∃ localsSize stackMax safe peak,
      DataSem.evaluate (compile program .ln).1 source =
        (some (.err (.abort reason)), { sourceNext with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }) := by
  obtain ⟨targetNext, targetRun, related⟩ :=
    compile_sameResult program .ln source sourceNext (some (.err (.abort reason))) run (by simpa using notType)
  have sourceControl := evaluate_abort_control program source sourceNext reason notType run
  have targetControl := evaluate_abort_control (compile program .ln).1 source targetNext reason notType targetRun
  have localsEq : sourceNext.locals = targetNext.locals := sourceControl.1.trans targetControl.1.symm
  have stackEq : sourceNext.stack = targetNext.stack := sourceControl.2.trans targetControl.2.symm
  have stateEq : targetNext = { sourceNext with localsSize := targetNext.localsSize, stackMax := targetNext.stackMax, safeForSpace := targetNext.safeForSpace, peakHeapLength := targetNext.peakHeapLength } := by
    rcases related with ⟨code, clock, space, ffi, refs, global, handler, _, compiler, oracle, stamps, limits, frames, _⟩
    cases sourceNext
    cases targetNext
    simp_all
  refine ⟨targetNext.localsSize, targetNext.stackMax, targetNext.safeForSpace, targetNext.peakHeapLength, ?_⟩
  rw [← stateEq]
  exact targetRun

/-- The final-state data liveness correctness statement for every stopped,
non-type-error execution. It remains untagged until the data evaluator and
state carrier have been reviewed against HOL. -/
theorem compile_correct_stopped {C F : Type} (program : DataLang.Prog) (source sourceNext : State C F)
    (result : Result (List DataSem.Value) DataSem.Value)
    (run : DataSem.evaluate program source = (some result, sourceNext))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ localsSize stackMax safe peak,
      DataSem.evaluate (compile program .ln).1 source =
        (some result, { sourceNext with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }) := by
  cases result with
  | val values => exact compile_correct_value program source sourceNext values run
  | err error =>
    cases error with
    | raise value => exact compile_correct_raise program source sourceNext value run
    | abort reason => exact compile_correct_abort program source sourceNext reason (by simpa using notType) run

/-- The data liveness correctness statement in the source theorem's
evaluation-pair form. Its stopped/non-type-error premises, result, and four
updated state fields match the source statement. The data state has the same
fields as the source record, and the evaluator's force singleton pattern
corresponds to the source's length-one test. This remains untagged: the
transitive primitive semantics and the data-program and FFI carriers have not
completed the required typed correspondence review. -/
theorem compile_correct {C F : Type} (program : DataLang.Prog) (source : State C F)
    (notType : (DataSem.evaluate program source).1 ≠ some (.err (.abort .typeError)))
    (stopped : (DataSem.evaluate program source).1 ≠ none) :
    ∃ localsSize stackMax safe peak,
      DataSem.evaluate (compile program .ln).1 source =
        ((DataSem.evaluate program source).1,
          { (DataSem.evaluate program source).2 with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }) := by
  cases run : DataSem.evaluate program source with
  | mk outcome sourceNext =>
    cases outcome with
    | none => simp [run] at stopped
    | some result =>
      have noType : result ≠ .err (.abort .typeError) := by simpa [run] using notType
      obtain ⟨localsSize, stackMax, safe, peak, correct⟩ := compile_correct_stopped program source sourceNext result run noType
      exact ⟨localsSize, stackMax, safe, peak, by simpa only [run] using correct⟩

end Flapjack.Compiler.Backend.DataLive
