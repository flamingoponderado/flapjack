import Flapjack.Compiler.Backend.BviLet.Proofs.Environment
import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateList

/-! Evaluation of the variable deletion used by the BVI let optimizer. -/
namespace Flapjack.Compiler.Backend.BviLet.Proofs
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- A successful singleton remains successful after deleting a variable,
with the same state. This is Flapjack infrastructure for the list proof. -/
theorem evaluate_deleteVar_success {C F : Type} (expression : Bvi.Exp)
    (env : List Value) (state next : BviState C F) (values : List Value)
    (run : evaluate [expression] env state = (.val values, next)) :
    ∃ output, evaluate [deleteVar expression] env state = (.val output, next) := by
  cases expression with
  | var index =>
    cases lookup : env[index]? with
    | none => simp [evaluate, lookup] at run
    | some value =>
      simp [evaluate, lookup] at run
      obtain ⟨_, rfl⟩ := run
      refine ⟨[.number 0], ?_⟩
      change evaluate [.op (.intOp (.const 0)) []] env state = (.val [.number 0], state)
      simp [evaluate, fixClock, doApp, doAppFallback, doAppAux, BackendCommon.smallEnoughInt]
  | _ => exact ⟨values, by simpa [deleteVar] using run⟩

/-- A successful binding supplies a new output and the lookup recorded by
its extracted displacement. This is a helper for the list simulation. -/
theorem evaluate_deleteVar_head_rel {C F : Type} (expression : Bvi.Exp)
    (tail : List Bvi.Exp) (env outputValues : List Value)
    (state next : BviState C F) (value : Value)
    (run : evaluate [expression] env state = (.val [value], next))
    (lengths : outputValues.length = tail.length) :
    ∃ output, evaluate [deleteVar expression] env state = (.val [output], next) ∧
      (output :: (outputValues ++ env))[extract expression tail]? = some value := by
  cases expression with
  | var index =>
    cases lookup : env[index]? with
    | none => simp [evaluate, lookup] at run
    | some found =>
      simp [evaluate, lookup] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨.number 0, ?_, ?_⟩
      · change evaluate [.op (.intOp (.const 0)) []] env state = (.val [.number 0], state)
        simp [evaluate, fixClock, doApp, doAppFallback, doAppAux, BackendCommon.smallEnoughInt]
      · simp only [extract, List.getElem?_cons_succ]
        rw [List.getElem?_append_right (by omega)]
        simpa [lengths, Nat.add_comm] using lookup
  | _ => exact ⟨value, by simpa [deleteVar] using run, by simp [extract]⟩

/-- Successful deletion returns a related environment and preserves the
final state. Untagged until the BVI evaluator and dispatcher are reviewed. -/
theorem evaluate_deleteVar_list_success {C F : Type} (expressions : List Bvi.Exp)
    (targetEnv sourceEnv : List Value) (state final : BviState C F) (values : List Value)
    (offsets : List Nat) (d : Nat)
    (run : evaluateTuple (expressions, targetEnv, state) = (.val values, final))
    (related : envRel offsets d sourceEnv targetEnv) :
    ∃ output, evaluateTuple (expressions.map deleteVar, targetEnv, state) = (.val output, final) ∧
      envRel (extractList expressions ++ offsets) d (values ++ sourceEnv) (output ++ targetEnv) := by
  induction expressions generalizing state values with
  | nil =>
    simp [evaluateTuple, evaluate] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨[], by simp [evaluateTuple, evaluate], by simpa [extractList] using related⟩
  | cons head tail ih =>
    rw [evaluateCons] at run
    cases headRun : evaluateTuple ([head], targetEnv, state) with
    | mk headResult middle =>
      cases headResult with
      | err error => simp [headRun] at run
      | val headValues =>
        obtain ⟨value, rfl⟩ := evaluateSing head targetEnv state middle headValues headRun
        simp only [headRun] at run
        cases tailRun : evaluateTuple (tail, targetEnv, middle) with
        | mk tailResult last =>
          cases tailResult with
          | err error => simp [tailRun] at run
          | val tailValues =>
            simp [tailRun, Flapjack.holHd] at run
            rcases run with ⟨rfl, rfl⟩
            obtain ⟨outputs, outputRun, tailRel⟩ := ih middle tailValues tailRun
            have outputLength := evaluateImpLength (tail.map deleteVar) targetEnv middle last outputs outputRun
            simp only [List.length_map] at outputLength
            obtain ⟨output, transformedHead, headRel⟩ :=
              evaluate_deleteVar_head_rel head tail targetEnv outputs state middle value headRun outputLength.symm
            refine ⟨output :: outputs, ?_, ?_⟩
            · simp only [List.map_cons]
              rw [evaluateCons]
              change evaluateTuple ([deleteVar head], targetEnv, state) = (.val [output], middle) at transformedHead
              simp [transformedHead, outputRun, Flapjack.holHd]
            · simp only [extractList, List.cons_append, envRel]
              exact ⟨headRel, tailRel⟩

/-- Deleting variable aliases preserves a non-type-error list failure and
its final state. Untagged until the BVI evaluator and dispatcher are reviewed. -/
theorem evaluate_deleteVar_list_error {C F : Type} (expressions : List Bvi.Exp)
    (env : List Value) (state final : BviState C F)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult ExnOrRet)
    (run : evaluateTuple (expressions, env, state) = (.err error, final))
    (notTypeError : error ≠ .abort .typeError) :
    evaluateTuple (expressions.map deleteVar, env, state) = (.err error, final) := by
  induction expressions generalizing state with
  | nil => simp [evaluateTuple, evaluate] at run
  | cons head tail ih =>
    rw [evaluateCons] at run
    simp only [List.map_cons]
    rw [evaluateCons]
    cases headRun : evaluateTuple ([head], env, state) with
    | mk headResult next =>
      cases headResult with
      | err headError =>
        simp [headRun] at run
        rcases run with ⟨rfl, rfl⟩
        have transformed : evaluateTuple ([deleteVar head], env, state) = (.err headError, next) :=
          evaluate_deleteVar_error head env state next headError headRun notTypeError
        rw [transformed]
      | val values =>
        have headRun' : evaluate [head] env state = (.val values, next) := headRun
        obtain ⟨output, transformedHead⟩ := evaluate_deleteVar_success head env state next values headRun'
        change evaluateTuple ([deleteVar head], env, state) = (.val output, next) at transformedHead
        simp only [headRun] at run
        rw [transformedHead]
        cases tailRun : evaluateTuple (tail, env, next) with
        | mk tailResult last =>
          cases tailResult with
          | val tailValues => simp [tailRun] at run
          | err tailError =>
            simp [tailRun] at run
            rcases run with ⟨rfl, rfl⟩
            dsimp only
            rw [ih next tailRun]

end Flapjack.Compiler.Backend.BviLet.Proofs
