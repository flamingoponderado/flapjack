import Flapjack.Compiler.Backend.BvlHandle.Helpers
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyError

/-! Soundness of the handler compiler's syntactic raise analysis. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A non-raising operation has a non-raising argument list. -/
theorem canRaise_op_args_false (op : ClosLang.Op) (args : List Bvl.Exp)
    (safe : canRaise (.op op args) = false) : canRaiseList args = false := by
  cases op <;> try simp_all [canRaise]
  case thunkOp operation => cases operation <;> simp_all [canRaise]

/-- Primitive application never returns a raised value. -/
theorem doApp_not_raise {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) (value : Value) : doApp op args state ≠ .err (.raise value) := by
  intro run
  have impossible := BvlProps.doAppError op args state (.raise value) run
  simp at impossible

/-- If a list is classified as unable to raise, its evaluation cannot return
a raised value. This remains untagged pending evaluator source review. -/
theorem evaluate_not_raise_of_canRaiseList_false {C F : Type} (expressions : List Bvl.Exp)
    (env : List Value) (state : State C F) (value : Value)
    (safe : canRaiseList expressions = false) :
    (evaluate expressions env state).1 ≠ .err (.raise value) := by
  have allWeights : ∀ weight : Nat, ∀ (expressions : List Bvl.Exp)
      (env : List Value) (state : State C F) (value : Value),
      expsWeight expressions = weight → canRaiseList expressions = false →
      (evaluate expressions env state).1 ≠ .err (.raise value) := by
    intro weight
    induction weight using Nat.strongRecOn with
    | ind weight ih =>
      intro expressions env state value measure safe
      cases expressions with
      | nil => simp [evaluate]
      | cons first rest =>
        cases rest with
        | cons second tail =>
          simp only [canRaiseList, Bool.or_eq_false_iff] at safe
          have headSafe : canRaiseList [first] = false := by simpa [canRaiseList] using safe.1
          have headIH := ih (expsWeight [first]) (by simp only [expsWeight] at measure ⊢; omega)
            [first] env state value rfl headSafe
          rw [evaluate, fixClock_evaluate]
          cases headRun : evaluate [first] env state with
          | mk result next =>
            simp only [headRun] at headIH
            cases result with
            | err error => simpa using headIH
            | val values =>
              have tailIH := ih (expsWeight (second :: tail)) (by simp only [expsWeight] at measure ⊢; omega)
                (second :: tail) env next value rfl (by simpa [canRaiseList] using safe.2)
              cases tailRun : evaluate (second :: tail) env next with
              | mk tailResult last =>
                simp only [tailRun] at tailIH
                cases tailResult <;> simp_all
        | nil =>
          simp only [canRaiseList, Bool.or_false] at safe
          cases first with
          | var index => simp [evaluate]; split <;> simp
          | raise body => simp [canRaise] at safe
          | force loc index => simp [canRaise] at safe
          | call ticks dest args => simp [canRaise] at safe
          | tick body =>
            simp only [canRaise] at safe
            rw [evaluate]
            split
            · simp
            · exact ih (expsWeight [body]) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                [body] env (decClock 1 state) value rfl (by simpa [canRaiseList] using safe)
          | handle body handler =>
            simp only [canRaise] at safe
            rw [evaluate, fixClock_evaluate]
            cases bodyRun : evaluate [body] env state with
            | mk result next =>
              cases result with
              | val values => simp
              | err error =>
                cases error with
                | abort reason => simp
                | raise raised =>
                  exact ih (expsWeight [handler]) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                    [handler] (raised :: env) next value rfl (by simpa [canRaiseList] using safe)
          | «let» bindings body =>
            simp only [canRaise, Bool.or_eq_false_iff] at safe
            have bindingsIH := ih (expsWeight bindings) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
              bindings env state value rfl safe.2
            rw [evaluate, fixClock_evaluate]
            cases bindingsRun : evaluate bindings env state with
            | mk result next =>
              simp only [bindingsRun] at bindingsIH
              cases result with
              | err error => simpa using bindingsIH
              | val values =>
                exact ih (expsWeight [body]) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                  [body] (values ++ env) next value rfl (by simpa [canRaiseList] using safe.1)
          | ifThenElse condition yes no =>
            simp only [canRaise, Bool.or_eq_false_iff] at safe
            have conditionIH := ih (expsWeight [condition]) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
              [condition] env state value rfl (by simpa [canRaiseList] using safe.1.1)
            rw [evaluate, fixClock_evaluate]
            cases conditionRun : evaluate [condition] env state with
            | mk result next =>
              simp only [conditionRun] at conditionIH
              cases result with
              | err error => simpa using conditionIH
              | val values =>
                dsimp only
                split
                · simp
                · exact ih (expsWeight [yes]) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                    [yes] env next value rfl (by simpa [canRaiseList] using safe.1.2)
                · exact ih (expsWeight [no]) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                    [no] env next value rfl (by simpa [canRaiseList] using safe.2)
          | op op args =>
            have argsSafe := canRaise_op_args_false op args safe
            have argsIH := ih (expsWeight args) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
              args env state value rfl argsSafe
            rw [evaluate, fixClock_evaluate]
            cases argsRun : evaluate args env state with
            | mk result next =>
              simp only [argsRun] at argsIH
              cases result with
              | err error => simpa using argsIH
              | val values =>
                cases appRun : doApp op values.reverse next with
                | val pair => cases pair; simp [appRun]
                | err error =>
                  simp only [appRun]
                  intro equal
                  have errEq : error = .raise value := by simpa using equal
                  subst error
                  exact doApp_not_raise op values.reverse next value appRun
  exact allWeights (expsWeight expressions) expressions env state value rfl safe

/-- A raised result implies the source handler pass marks the singleton or
expression list as potentially raising. This is untagged pending evaluator
source review and representation qualification. -/
theorem canRaise_of_evaluate {C F : Type} :
    (∀ (expression : Bvl.Exp) (env : List Value) (state final : State C F) (value : Value),
      evaluate [expression] env state = (.err (.raise value), final) → canRaise expression = true) ∧
    (∀ (expressions : List Bvl.Exp) (env : List Value) (state final : State C F) (value : Value),
      evaluate expressions env state = (.err (.raise value), final) → canRaiseList expressions = true) := by
  constructor
  · intro expression env state final value run
    cases safe : canRaise expression with
    | true => rfl
    | false =>
      have impossible := evaluate_not_raise_of_canRaiseList_false [expression] env state value
        (by simpa [canRaiseList] using safe)
      exact False.elim (impossible (by rw [run]))
  · intro expressions env state final value run
    cases safe : canRaiseList expressions with
    | true => rfl
    | false =>
      exact False.elim (evaluate_not_raise_of_canRaiseList_false expressions env state value safe (by rw [run]))

end Flapjack.Compiler.Backend.BvlHandle.Proofs
