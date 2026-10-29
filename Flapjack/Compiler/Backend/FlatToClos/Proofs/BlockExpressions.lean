import Flapjack.Compiler.Backend.FlatToClos.Proofs.BlockOperations
import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases

/-! Block-test expression cases for the proof-side pass simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- A unary length test evaluates to related Boolean values when its operand
is simulated and the source expression avoids a type error. -/
theorem evaluate_lenEq {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (expected : Nat) (argument : FlatLang.Exp)
    (argSim : EvalSim env names values source target [argument])
    (notTypeError : (FlatSem.evaluate env source [.app trace (.lenEq expected) [argument]]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.lenEq expected) [argument]] := by
  have flatFix := (FlatSem.fixClock_evaluations env source [argument] argument []).1
  have closFix := ClosSem.fixClock_evaluate [compileExp names argument] values target
  unfold EvalSim at argSim ⊢
  simp only [compile, compileExps, compileExp, compileOp, List.reverse_singleton] at argSim ⊢
  rw [FlatSem.evaluate] at notTypeError ⊢
  rw [ClosSem.evaluate, closFix]
  simp only [List.reverse_singleton, flatFix] at notTypeError ⊢
  cases flatRun : FlatSem.evaluate env source [argument] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names argument] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argSim notTypeError ⊢
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
            cases head <;> simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat,
              ClosSem.doApp, ClosSem.applyBlock] at notTypeError ⊢
            all_goals rename_i related
            all_goals have sameLength : _ := related.length_eq
            all_goals rw [← sameLength]
            all_goals exact ⟨states, .value (.cons (boolValue_related _) .nil)⟩

/-- A constructor tag-and-length test evaluates to related Boolean values. -/
theorem evaluate_tagLenEq {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (tag expected : Nat) (argument : FlatLang.Exp)
    (argSim : EvalSim env names values source target [argument])
    (notTypeError : (FlatSem.evaluate env source [.app trace (.tagLenEq tag expected) [argument]]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.tagLenEq tag expected) [argument]] := by
  have flatFix := (FlatSem.fixClock_evaluations env source [argument] argument []).1
  have closFix := ClosSem.fixClock_evaluate [compileExp names argument] values target
  unfold EvalSim at argSim ⊢
  simp only [compile, compileExps, compileExp, compileOp, List.reverse_singleton] at argSim ⊢
  rw [FlatSem.evaluate] at notTypeError ⊢
  rw [ClosSem.evaluate, closFix]
  simp only [List.reverse_singleton, flatFix] at notTypeError ⊢
  cases flatRun : FlatSem.evaluate env source [argument] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names argument] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argSim notTypeError ⊢
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
            cases head <;> simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat,
              ClosSem.doApp, ClosSem.applyBlock] at notTypeError ⊢
            rename_i related
            have sameLength := related.length_eq
            rw [← sameLength]
            exact ⟨states, .value (.cons (boolValue_related _) .nil)⟩

end Flapjack.Compiler.Backend.FlatToClos
