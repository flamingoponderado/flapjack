import Flapjack.Compiler.Backend.FlatToClos.Proofs.Memory
import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases

/-! Reference-expression cases for the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- Unary reference allocation creates related source and closure stores. -/
theorem evaluate_ref {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (argument : FlatLang.Exp)
    (argSim : EvalSim env names values source target [argument]) :
    EvalSim env names values source target [.app trace (.src .opref) [argument]] := by
  have flatFix := (FlatSem.fixClock_evaluations env source [argument] argument []).1
  have closFix := ClosSem.fixClock_evaluate [compileExp names argument] values target
  unfold EvalSim at argSim ⊢
  simp only [compile, compileExps, compileExp, compileOp, List.reverse_singleton] at argSim ⊢
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [List.reverse_singleton, flatFix]
  cases flatRun : FlatSem.evaluate env source [argument] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names argument] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argSim ⊢
      rcases argSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length env source next argument _ flatRun
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            rename_i sourceValue targetValue
            have index := leastUnusedRef_eq_length next.refs nextTarget.refs states.2.2.2.1
            have updated := stateRel_allocRef next nextTarget sourceValue targetValue states head
            simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
              storeAlloc, ClosSem.doApp, ClosSem.applyMemory, index, updated,
              EvalResultRel.value (.cons (ValueRel.loc true next.refs.length) .nil)]

end Flapjack.Compiler.Backend.FlatToClos
