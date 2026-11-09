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

/-- At every clock, successful or non-type-error evaluation from the empty
code store is simulated by the annotation pass with its adapted compiler and
oracle. This is a proof-side consequence, not a whole-compiler theorem. -/
theorem initial_evaluate_annotated {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) (program : List ClosLang.Exp)
    (result : Result (List Value) Value) (next : State C F)
    (run : evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) clock) =
      (result, next))
    (noType : result ≠ .err (.abort .typeError)) (safe : everyFnVarsNone program)
    (oracleSafe : ∀ n, everyFnVarsNone (oracle n).2.1 ∧
      everyFnVarsNone ((oracle n).2.2.map (fun (_, _, body) => body))) :
    ∃ targetResult targetNext,
      evaluate (annotateList 0 program) []
        (initialState ffi maxApp HolFiniteMapExact.empty (pureCo compileInc ∘ oracle) compiler clock) =
          (targetResult, targetNext) ∧ ResultRel result targetResult ∧ StateRel next targetNext := by
  apply annotate_correct program _ _ [] result next run noType safe
  · simp [CodeSafe, initialState, HolFiniteMapExact.empty]
  · exact oracleSafe
  · exact initialState_related ffi maxApp clock oracle compiler

end Flapjack.Compiler.Backend.ClosAnnotate
