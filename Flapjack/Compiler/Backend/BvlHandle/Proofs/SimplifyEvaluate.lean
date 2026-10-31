import Flapjack.Compiler.Backend.BvlHandle.Proofs.AdjustEvaluate
import Flapjack.Compiler.Backend.BvlHandle.Proofs.CanRaise
import Flapjack.Compiler.Backend.BvlHandle.Proofs.Simplify
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateLength

/-! Local semantic rewrites used by handler simplification. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.BvlSem

/-- If an operand cannot raise, handling its explicit raise is equivalent to
binding its value and executing the handler. -/
theorem evaluate_handle_raise_as_let {C F : Type} (operand handler : Bvl.Exp)
    (env : List Value) (state : State C F) (safe : canRaise operand = false) :
    evaluate [.handle (.raise operand) handler] env state =
      evaluate [.let [operand] handler] env state := by
  have noRaise : ∀ value, (evaluate [operand] env state).1 ≠ .err (.raise value) := by
    intro value
    apply evaluate_not_raise_of_canRaiseList_false [operand] env state value
    simpa [canRaiseList] using safe
  rw [evaluate, fixClock_evaluate, evaluate, fixClock_evaluate]
  cases operandRun : evaluate [operand] env state with
  | mk result next =>
    simp only [operandRun] at noRaise
    cases result with
    | err error =>
      cases error with
      | abort reason => simp [evaluate, operandRun]
      | raise value => exact False.elim (noRaise value rfl)
    | val values =>
      obtain ⟨value, rfl⟩ := BvlSem.evaluate_singleton operand env state next values operandRun
      simp [evaluate, operandRun]

/-- The `raise` branch of `makeHandle` preserves evaluation when recursive
simplification preserves its operand and handler. -/
theorem evaluate_makeHandle_raise {C F : Type} (operand handler : Bvl.Exp) (depth : Nat)
    (env : List Value) (state : State C F)
    (bound : depth ≤ env.length)
    (operandIH : ∀ (env : List Value) (state : State C F), evaluate [handleSimp operand] env state = evaluate [operand] env state)
    (handlerIH : ∀ (env : List Value) (state : State C F), evaluate [handleSimp handler] env state = evaluate [handler] env state) :
    evaluate [makeHandle (.raise operand) handler depth] env state =
      evaluate [.handle (.raise operand) (handleAdjVars 1 depth handler)] env state := by
  have adjusted : ∀ (value : Value) (next : State C F),
      evaluate [handleAdjVars 1 depth (handleSimp handler)] (value :: env) next =
        evaluate [handleAdjVars 1 depth handler] (value :: env) next := by
    intro value next
    apply handleAdjVars_evaluate_congr _ _ 1 depth (value :: env) next
    · exact fun env => handlerIH env next
    · simp only [List.length_cons]; omega
  cases raises : canRaise operand with
  | true =>
    simp only [makeHandle, raises, ↓reduceIte, handleSimp]
    simp only [evaluate, operandIH]
    repeat' split <;> simp_all
  | false =>
    simp only [makeHandle, raises, Bool.false_eq_true, ↓reduceIte]
    rw [← evaluate_handle_raise_as_let operand (handleAdjVars 1 depth (handleSimp handler)) env state raises]
    simp only [evaluate]
    repeat' split <;> simp_all

/-- If the bindings cannot raise, a handler can move into the let body;
its adjusted variables account for the newly bound values. -/
theorem evaluate_handle_let_push {C F : Type} (bindings : List Bvl.Exp)
    (body handler : Bvl.Exp) (depth : Nat) (env : List Value) (state : State C F)
    (bound : depth ≤ env.length) (safe : canRaiseList bindings = false) :
    evaluate [.handle (.let bindings body) (handleAdjVars 1 depth handler)] env state =
      evaluate [.let bindings (.handle body (handleAdjVars 1 (depth + bindings.length) handler))] env state := by
  have noRaise : ∀ value, (evaluate bindings env state).1 ≠ .err (.raise value) := by
    intro value
    exact evaluate_not_raise_of_canRaiseList_false bindings env state value safe
  rw [evaluate, fixClock_evaluate, evaluate, fixClock_evaluate]
  cases bindingsRun : evaluate bindings env state with
  | mk result next =>
    have clockBound : next.clock ≤ state.clock := by
      have clock := evaluate_clock_le bindings env state
      simpa [bindingsRun] using clock
    simp only [bindingsRun] at noRaise
    cases result with
    | err error =>
      cases error with
      | abort reason => simp [evaluate, bindingsRun, fixClock, Nat.min_eq_right clockBound]
      | raise value => exact False.elim (noRaise value rfl)
    | val values =>
      have len := BvlProps.evaluateImpLength bindings env state values next bindingsRun
      simp only [evaluate, bindingsRun, fixClock, Nat.min_eq_right clockBound]
      cases bodyRun : evaluate [body] (values ++ env) next with
      | mk bodyResult after =>
        have bodyBound : after.clock ≤ next.clock := by
          have clock := evaluate_clock_le [body] (values ++ env) next
          simpa [bodyRun] using clock
        cases bodyResult with
        | val returned => simp [Nat.min_eq_right bodyBound]
        | err error =>
          cases error with
          | abort reason => simp [Nat.min_eq_right bodyBound]
          | raise value =>
            have shifted := evaluate_handleAdjVars_extend handler depth [value] values env after bound
            simp only [List.length_singleton, List.cons_append, List.nil_append, ← len] at shifted
            simpa [bodyRun, fixClock, Nat.min_eq_right bodyBound] using shifted.symm

/-- The `let` branch of `makeHandle` preserves evaluation, using the
recursive simplification and handler-pushing hypotheses. -/
theorem evaluate_makeHandle_let {C F : Type} (bindings : List Bvl.Exp)
    (body handler : Bvl.Exp) (depth : Nat) (env : List Value) (state : State C F)
    (bound : depth ≤ env.length)
    (bindingsIH : ∀ (env : List Value) (state : State C F),
      evaluate (handleSimpList bindings) env state = evaluate bindings env state)
    (bodyIH : ∀ (env : List Value) (state : State C F),
      evaluate [handleSimp body] env state = evaluate [body] env state)
    (handlerIH : ∀ (env : List Value) (state : State C F),
      evaluate [handleSimp handler] env state = evaluate [handler] env state)
    (makeIH : ∀ (newDepth : Nat) (newEnv : List Value) (next : State C F), newDepth ≤ newEnv.length →
      evaluate [makeHandle body handler newDepth] newEnv next =
        evaluate [.handle body (handleAdjVars 1 newDepth handler)] newEnv next) :
    evaluate [makeHandle (.let bindings body) handler depth] env state =
      evaluate [.handle (.let bindings body) (handleAdjVars 1 depth handler)] env state := by
  have adjusted : ∀ (value : Value) (next : State C F),
      evaluate [handleAdjVars 1 depth (handleSimp handler)] (value :: env) next =
        evaluate [handleAdjVars 1 depth handler] (value :: env) next := by
    intro value next
    apply handleAdjVars_evaluate_congr _ _ 1 depth (value :: env) next
    · exact fun env => handlerIH env next
    · simp only [List.length_cons]; omega
  cases raises : canRaiseList bindings with
  | true =>
    simp only [makeHandle, raises, ↓reduceIte, handleSimp]
    simp only [evaluate, bindingsIH, bodyIH]
    repeat' split <;> simp_all
  | false =>
    rw [evaluate_handle_let_push bindings body handler depth env state bound raises]
    simp only [makeHandle, raises, Bool.false_eq_true, ↓reduceIte]
    rw [evaluate, fixClock_evaluate, evaluate, fixClock_evaluate, bindingsIH]
    cases bindingsRun : evaluate bindings env state with
    | mk result next =>
      cases result with
      | err error => rfl
      | val values =>
        have len := BvlProps.evaluateImpLength bindings env state values next bindingsRun
        apply makeIH (depth + bindings.length) (values ++ env) next
        simp only [List.length_append, len]
        omega

end Flapjack.Compiler.Backend.BvlHandle.Proofs
