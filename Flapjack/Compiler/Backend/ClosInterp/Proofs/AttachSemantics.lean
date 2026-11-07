import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallSimulationFull
import Flapjack.Compiler.Backend.Semantics.ClosSem.Semantics
import Flapjack.Compiler.Backend.Semantics.ClosSem.SemanticsSimulation
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateEventsClockFull

/-! Interpreter insertion observations for the proof-side closure evaluator.
The evaluator and its state carriers await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps

/-- Interpreter attachment simulates either installation branch at some
target clock extension and preserves the FFI state and evaluation result. -/
theorem attachInterpreter_initial_observation {C F : Type} (expressions : List ClosLang.Exp)
    (ffi : HolFfiState F) (maxApp clock : Nat) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C) (sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (oracleSafe : ∀ index, (oracle index).2.2 = []) (positive : 1 ≤ maxApp)
    (run : ClosSem.evaluate (attachInterpreter expressions) []
      (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc insertProgram compiler) clock) = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate (attachInterpreter expressions) []
        (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle) compiler (extra + clock)) =
        (result, targetFinal) ∧ sourceFinal.ffi = targetFinal.ffi := by
  cases needs : ClosLang.hasInstallList expressions with
  | false =>
    obtain ⟨targetFinal, targetRun, related, _⟩ :=
      attachInterpreter_noInstall_initial_simulation expressions ffi maxApp clock oracle compiler sourceFinal result needs oracleSafe positive run
    refine ⟨0, targetFinal, by simpa using targetRun, ?_⟩
    rw [stateRel1_replaceCompiler sourceFinal targetFinal related.1]
  | true =>
    obtain ⟨extra, targetFinal, targetRun, related⟩ :=
      attachInterpreter_initial_simulation expressions ffi maxApp clock oracle compiler sourceFinal result needs oracleSafe positive run notTypeError
    refine ⟨extra, targetFinal, ?_, ?_⟩
    · simpa [ClosSem.initialState] using targetRun
    · rw [stateRel_replaceCompiler sourceFinal targetFinal related]

/-- Attached programs without installation have identical proof-side
observational semantics under the two initial compiler configurations. -/
theorem attachInterpreter_noInstall_semantics {C F : Type} (expressions : List ClosLang.Exp)
    (ffi : HolFfiState F) (maxApp : Nat) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C) (safe : ClosLang.hasInstallList expressions = false)
    (oracleSafe : ∀ index, (oracle index).2.2 = []) (positive : 1 ≤ maxApp) :
    ClosSem.semantics ffi maxApp HolFiniteMapExact.empty oracle (pureCc insertProgram compiler) (attachInterpreter expressions) =
      ClosSem.semantics ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle) compiler (attachInterpreter expressions) := by
  apply ClosSem.semantics_eq_of_same_observations
  intro clock
  cases sourceRun : ClosSem.evaluate (attachInterpreter expressions) []
      (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc insertProgram compiler) clock) with
  | mk result sourceFinal =>
    obtain ⟨targetFinal, targetRun, related, _⟩ :=
      attachInterpreter_noInstall_initial_simulation expressions ffi maxApp clock oracle compiler sourceFinal result safe oracleSafe positive sourceRun
    have ffiEq : sourceFinal.ffi = targetFinal.ffi := by
      rw [stateRel1_replaceCompiler sourceFinal targetFinal related.1]
    simp [targetRun, ffiEq]

/-- If the source observation does not fail, attaching the interpreter
also cannot introduce a target type error and preserves all terminating
observations, whether or not the program uses installation. -/
theorem attachInterpreter_terminating_observations {C F : Type} (expressions : List ClosLang.Exp)
    (ffi : HolFfiState F) (maxApp : Nat) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C) (oracleSafe : ∀ index, (oracle index).2.2 = [])
    (positive : 1 ≤ maxApp)
    (sourceNoFail : ClosSem.semantics ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc insertProgram compiler) (attachInterpreter expressions) ≠ .fail) :
    ClosSem.semantics ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle)
        compiler (attachInterpreter expressions) ≠ .fail ∧
      ClosSem.terminatingObservation ffi maxApp HolFiniteMapExact.empty oracle
        (pureCc insertProgram compiler) (attachInterpreter expressions) =
      ClosSem.terminatingObservation ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle)
        compiler (attachInterpreter expressions) := by
  have sourceSafe := (ClosSem.semantics_ne_fail_iff ffi maxApp HolFiniteMapExact.empty oracle
    (pureCc insertProgram compiler) (attachInterpreter expressions)).1 sourceNoFail
  have simulation : ∀ clock result final,
      ClosSem.evaluate (attachInterpreter expressions) []
        (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc insertProgram compiler) clock) = (result, final) →
      ∃ extra targetFinal, ClosSem.evaluate (attachInterpreter expressions) []
        (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle) compiler (clock + extra)) =
          (result, targetFinal) ∧ final.ffi = targetFinal.ffi := by
    intro clock result final run
    have notTypeError : result ≠ .err (.abort .typeError) := by
      intro bad
      exact sourceSafe clock (by simpa [run] using bad)
    obtain ⟨extra, targetFinal, targetRun, ffiEq⟩ :=
      attachInterpreter_initial_observation expressions ffi maxApp clock oracle compiler final result oracleSafe positive run notTypeError
    exact ⟨extra, targetFinal, by simpa [Nat.add_comm] using targetRun, ffiEq⟩
  constructor
  · apply (ClosSem.semantics_ne_fail_iff ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle)
      compiler (attachInterpreter expressions)).2
    exact ClosSem.simulation_target_noTypeError ffi maxApp HolFiniteMapExact.empty oracle (pureCo insertProgram ∘ oracle)
      (pureCc insertProgram compiler) compiler (attachInterpreter expressions) sourceSafe simulation
  · exact ClosSem.simulation_terminatingObservation_eq ffi maxApp HolFiniteMapExact.empty oracle (pureCo insertProgram ∘ oracle)
      (pureCc insertProgram compiler) compiler (attachInterpreter expressions) simulation

/-- The interpreter insertion simulation preserves all proof-side behavior
once the evaluator's clock-indexed event traces are known to be monotone.
The unconditional trace monotonicity result is applied below. -/
theorem attachInterpreter_semantics_of_trace_monotonicity {C F : Type} (expressions : List ClosLang.Exp)
    (ffi : HolFfiState F) (maxApp : Nat) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C) (oracleSafe : ∀ index, (oracle index).2.2 = [])
    (positive : 1 ≤ maxApp)
    (sourceNoFail : ClosSem.semantics ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc insertProgram compiler) (attachInterpreter expressions) ≠ .fail)
    (sourceMono : ∀ k l, k ≤ l →
      (ClosSem.evaluate (attachInterpreter expressions) []
        (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc insertProgram compiler) k)).2.ffi.ioEvents <+:
      (ClosSem.evaluate (attachInterpreter expressions) []
        (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc insertProgram compiler) l)).2.ffi.ioEvents)
    (targetMono : ∀ k l, k ≤ l →
      (ClosSem.evaluate (attachInterpreter expressions) []
        (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle) compiler k)).2.ffi.ioEvents <+:
      (ClosSem.evaluate (attachInterpreter expressions) []
        (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle) compiler l)).2.ffi.ioEvents) :
    ClosSem.semantics ffi maxApp HolFiniteMapExact.empty oracle (pureCc insertProgram compiler) (attachInterpreter expressions) =
      ClosSem.semantics ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle) compiler (attachInterpreter expressions) := by
  have sourceSafe := (ClosSem.semantics_ne_fail_iff ffi maxApp HolFiniteMapExact.empty oracle
    (pureCc insertProgram compiler) (attachInterpreter expressions)).1 sourceNoFail
  apply ClosSem.semantics_eq_of_clocked_simulation _ _ _ _ _ _ _ _ sourceSafe ?_ sourceMono targetMono
  intro clock result final run
  have notTypeError : result ≠ .err (.abort .typeError) := by
    intro bad
    exact sourceSafe clock (by simpa [run] using bad)
  obtain ⟨extra, targetFinal, targetRun, ffiEq⟩ :=
    attachInterpreter_initial_observation expressions ffi maxApp clock oracle compiler final result oracleSafe positive run notTypeError
  exact ⟨extra, targetFinal, by simpa [Nat.add_comm] using targetRun, ffiEq⟩

/-- Interpreter attachment preserves the proof-side closure observations,
including divergence, when the source does not fail. The hypotheses and
equality direction follow `semantics_attach_interpreter`; this result is
untagged because correspondence of the evaluator and state carriers with HOL
has not yet been established. -/
theorem attachInterpreter_semantics {C F : Type} (expressions : List ClosLang.Exp)
    (ffi : HolFfiState F) (maxApp : Nat) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C)
    (sourceNoFail : ClosSem.semantics ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc insertProgram compiler) (attachInterpreter expressions) ≠ .fail)
    (assumptions : (∀ index, (oracle index).2.2 = []) ∧ 0 < maxApp) :
    ClosSem.semantics ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle) compiler (attachInterpreter expressions) =
      ClosSem.semantics ffi maxApp HolFiniteMapExact.empty oracle (pureCc insertProgram compiler) (attachInterpreter expressions) := by
  symm
  apply attachInterpreter_semantics_of_trace_monotonicity expressions ffi maxApp oracle compiler assumptions.1 assumptions.2 sourceNoFail
  · exact ClosSem.evaluate_initial_ioEvents_mono ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc insertProgram compiler) (attachInterpreter expressions)
  · exact ClosSem.evaluate_initial_ioEvents_mono ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle)
      compiler (attachInterpreter expressions)

end Flapjack.Compiler.Backend.ClosInterp
