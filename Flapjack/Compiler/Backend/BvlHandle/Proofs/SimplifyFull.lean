import Flapjack.Compiler.Backend.BvlHandle.Proofs.SimplifyEvaluate
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList
import Flapjack.Compiler.Backend.BvlHandle.Proofs.SimplifyProduction

/-! Evaluation correctness of the complete BVL handler simplifier. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.BvlSem

private theorem evaluate_handle_congr {C F : Type} (body body' handler handler' : Bvl.Exp)
    (env : List Value) (state : State C F)
    (bodyEq : evaluate [body] env state = evaluate [body'] env state)
    (handlerEq : ∀ (value : Value) (next : State C F),
      evaluate [handler] (value :: env) next = evaluate [handler'] (value :: env) next) :
    evaluate [.handle body handler] env state = evaluate [.handle body' handler'] env state := by
  rw [evaluate, fixClock_evaluate, evaluate, fixClock_evaluate, bodyEq]
  repeat' split <;> simp_all

mutual
/-- Handler simplification preserves evaluation of an expression. This stays
untagged pending review of the BVL evaluator's HOL correspondence. -/
theorem evaluate_handleSimp {C F : Type} (expression : Bvl.Exp)
    (env : List Value) (state : State C F) :
    evaluate [handleSimp expression] env state = evaluate [expression] env state := by
  cases expression with
  | var index => simp [handleSimp]
  | force location index => simp [handleSimp]
  | tick body =>
    simp only [handleSimp, evaluate]
    split
    · rfl
    · exact evaluate_handleSimp body env (decClock 1 state)
  | raise body =>
    simp only [handleSimp, evaluate, evaluate_handleSimp body env state]
  | op op args =>
    simp only [handleSimp, evaluate, evaluate_handleSimpList args env state]
  | call ticks dest args =>
    simp only [handleSimp, evaluate, evaluate_handleSimpList args env state]
  | ifThenElse condition yes no =>
    simp only [handleSimp]
    exact evaluate_if_congr _ _ _ _ _ _ env state
      (evaluate_handleSimp condition env state) (evaluate_handleSimp yes env) (evaluate_handleSimp no env)
  | «let» bindings body =>
    simp only [handleSimp, evaluate, evaluate_handleSimpList bindings env state]
    repeat' split <;> simp_all [evaluate_handleSimp body]
  | handle body handler =>
    simp only [handleSimp]
    have h := evaluate_makeHandle body handler 0 env state (by omega)
    rw [h]
    apply evaluate_handle_congr _ _ _ _ env state rfl
    intro value next
    simpa using evaluate_handleAdjVars handler [value] [] env next
termination_by handleSize expression
decreasing_by all_goals (simp only [handleSize]; omega)

/-- Handler simplification preserves evaluation of expression lists. -/
theorem evaluate_handleSimpList {C F : Type} (expressions : List Bvl.Exp)
    (env : List Value) (state : State C F) :
    evaluate (handleSimpList expressions) env state = evaluate expressions env state := by
  cases expressions with
  | nil => simp [handleSimpList]
  | cons first rest =>
    simp only [handleSimpList]
    change evaluateTuple (handleSimp first :: handleSimpList rest, env, state) =
      evaluateTuple (first :: rest, env, state)
    rw [BvlProps.evaluateCons (handleSimp first) (handleSimpList rest), BvlProps.evaluateCons first rest]
    simp only [evaluateTuple, evaluate_handleSimp first env state]
    repeat' split <;> simp_all [evaluate_handleSimpList rest env]
termination_by handleSizeList expressions
decreasing_by all_goals (simp only [handleSizeList]; omega)

/-- Pushing a handler through an expression preserves evaluation when the
variable-adjustment depth is available in the environment. -/
theorem evaluate_makeHandle {C F : Type} (body handler : Bvl.Exp) (depth : Nat)
    (env : List Value) (state : State C F) (bound : depth ≤ env.length) :
    evaluate [makeHandle body handler depth] env state =
      evaluate [.handle body (handleAdjVars 1 depth handler)] env state := by
  cases body with
  | raise operand =>
    apply evaluate_makeHandle_raise operand handler depth env state bound
    · exact evaluate_handleSimp operand
    · exact evaluate_handleSimp handler
  | «let» bindings body =>
    apply evaluate_makeHandle_let bindings body handler depth env state bound
    · exact evaluate_handleSimpList bindings
    · exact evaluate_handleSimp body
    · exact evaluate_handleSimp handler
    · intro newDepth newEnv next valid
      exact evaluate_makeHandle body handler newDepth newEnv next valid
  | ifThenElse condition yes no =>
    apply evaluate_makeHandle_if condition yes no handler depth env state bound
    · exact evaluate_handleSimp condition
    · exact evaluate_handleSimp yes
    · exact evaluate_handleSimp no
    · exact evaluate_handleSimp handler
    · intro next
      exact evaluate_makeHandle yes handler depth env next bound
    · intro next
      exact evaluate_makeHandle no handler depth env next bound
  | _ =>
    simp only [makeHandle]
    all_goals apply evaluate_handle_congr _ _ _ _ env state (evaluate_handleSimp _ env state)
    all_goals intro value next
    all_goals apply handleAdjVars_evaluate_congr _ _ 1 depth (value :: env) next
    all_goals try (intro env; exact evaluate_handleSimp handler env next)
    all_goals simp only [List.length_cons]; omega
termination_by handleSize body + handleSize handler
decreasing_by
  all_goals simp_wf
  all_goals try simp only [handleSize]
  all_goals have h := handleSize_nonzero handler
  all_goals try omega
end

/-- The executed bounded simplifier returns an expression with the same
evaluation as its input. -/
theorem evaluate_simplifyBounded {C F : Type} (fuel : Nat) (expression : Bvl.Exp)
    (env : List Value) (state : State C F) :
    ∃ simplified, simplifyBounded fuel expression = some simplified ∧
      evaluate [simplified] env state = evaluate [expression] env state :=
  ⟨handleSimp expression, simplifyBounded_eq fuel expression, evaluate_handleSimp expression env state⟩

end Flapjack.Compiler.Backend.BvlHandle.Proofs
