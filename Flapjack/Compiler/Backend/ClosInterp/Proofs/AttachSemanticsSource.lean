module

public import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallSimulationFull
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Semantics
public import Flapjack.Compiler.Backend.Semantics.ClosSem.SemanticsSimulation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateEventsClockFull
public import Flapjack.FiniteMap.EmptyExact

@[expose] public section


/-! Source-shaped interpreter attachment observation. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps

/-- Interpreter attachment simulates either installation branch at some
target clock extension and preserves the FFI state and evaluation result.
This Flapjack-specific helper combines the two branches of the HOL proof. -/
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
    · rw [stateRel1_replaceCompiler sourceFinal targetFinal related.1]

/-- Attaching the interpreter preserves closure behavior with the original
oracle and compiler transformation. `insertProgram` is insertion on the
first component paired with the identity on the auxiliary code. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "semantics_attach_interpreter"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem attachInterpreter_semantics_source {C F : Type} (expressions : List ClosLang.Exp)
    (ffi : HolFfiState F) (maxApp : Nat) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C)
    (sourceNoFail : ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (pureCc insertProgram compiler) (attachInterpreter expressions) ≠ .fail)
    (assumptions : (∀ index, (oracle index).2.2 = []) ∧ 0 < maxApp) :
    ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty (pureCo insertProgram ∘ oracle)
      compiler (attachInterpreter expressions) =
    ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (pureCc insertProgram compiler) (attachInterpreter expressions) := by
  symm
  have sourceSafe := (ClosSem.semantics_ne_fail_iff ffi maxApp HolFiniteMapExact.empty oracle
    (pureCc insertProgram compiler) (attachInterpreter expressions)).1 sourceNoFail
  apply ClosSem.semantics_eq_of_clocked_simulation _ _ _ _ _ _ _ _ sourceSafe ?_
    (ClosSem.evaluate_initial_ioEvents_mono ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc insertProgram compiler) (attachInterpreter expressions))
    (ClosSem.evaluate_initial_ioEvents_mono ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle)
      compiler (attachInterpreter expressions))
  intro clock result final run
  have notTypeError : result ≠ .err (.abort .typeError) := by
    intro bad
    exact sourceSafe clock (by simpa [run] using bad)
  obtain ⟨extra, targetFinal, targetRun, ffiEq⟩ :=
    attachInterpreter_initial_observation expressions ffi maxApp clock oracle compiler final result assumptions.1 assumptions.2 run notTypeError
  exact ⟨extra, targetFinal, by simpa [Nat.add_comm] using targetRun, ffiEq⟩


end Flapjack.Compiler.Backend.ClosInterp
