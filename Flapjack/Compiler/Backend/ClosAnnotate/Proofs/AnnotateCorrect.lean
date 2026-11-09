import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Evaluate

/-! Initial-program consequences of the candidate annotation simulation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Specialize the mutual evaluator simulation to an empty source
environment. The target environment is arbitrary, as in the source result.
This is untagged pending HOL evaluator and carrier correspondence review. -/
theorem annotate_correct {C F : Type} (program : List ClosLang.Exp) (source target : State C F)
    (targetEnv : List Value) (result : Result (List Value) Value) (next : State C F)
    (run : evaluate program [] source = (result, next))
    (noType : result ≠ .err (.abort .typeError))
    (safe : everyFnVarsNone program) (code : CodeSafe source) (oracle : OracleSafe source)
    (states : StateRel source target) :
    ∃ targetResult targetNext, evaluate (annotateList 0 program) targetEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel next targetNext := by
  have vars : ∀ n, altFv n program = true → EnvOk 0 0 .ln [] targetEnv n := by
    exact envSetDefault {n | altFv n program = true} targetEnv
  obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
    evaluate_simulation.1 program [] source targetEnv target result next 0 0 .ln run noType (by simp)
      vars safe code oracle states
  exact ⟨targetResult, targetNext, by simpa [annotateList, altFree] using targetRun, resultRel, nextRel⟩

end Flapjack.Compiler.Backend.ClosAnnotate
