import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallSimulationFull
import Flapjack.Compiler.Backend.Semantics.ClosSem.Semantics

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

end Flapjack.Compiler.Backend.ClosInterp
