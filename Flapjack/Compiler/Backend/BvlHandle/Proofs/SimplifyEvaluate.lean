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

/-- An expression known not to raise is unaffected by an enclosing handler. -/
theorem evaluate_handle_of_noRaise {C F : Type} (body handler : Bvl.Exp)
    (env : List Value) (state : State C F) (safe : canRaise body = false) :
    evaluate [.handle body handler] env state = evaluate [body] env state := by
  have noRaise : ∀ value, (evaluate [body] env state).1 ≠ .err (.raise value) := by
    intro value
    apply evaluate_not_raise_of_canRaiseList_false [body] env state value
    simpa [canRaiseList] using safe
  rw [evaluate, fixClock_evaluate]
  cases bodyRun : evaluate [body] env state with
  | mk result next =>
    simp only [bodyRun] at noRaise
    cases result with
    | val values => rfl
    | err error =>
      cases error with
      | abort reason => rfl
      | raise value => exact False.elim (noRaise value rfl)

/-- A handler distributes through a conditional whose test cannot raise. -/
theorem evaluate_handle_if_push {C F : Type} (condition yes no handler : Bvl.Exp)
    (env : List Value) (state : State C F) (safe : canRaise condition = false) :
    evaluate [.handle (.ifThenElse condition yes no) handler] env state =
      evaluate [.ifThenElse condition (.handle yes handler) (.handle no handler)] env state := by
  have noRaise : ∀ value, (evaluate [condition] env state).1 ≠ .err (.raise value) := by
    intro value
    apply evaluate_not_raise_of_canRaiseList_false [condition] env state value
    simpa [canRaiseList] using safe
  cases conditionRun : evaluate [condition] env state with
  | mk result next =>
    have bound : next.clock ≤ state.clock := by
      have clock := evaluate_clock_le [condition] env state
      simpa [conditionRun] using clock
    simp only [conditionRun] at noRaise
    cases result with
    | err error =>
      cases error with
      | abort reason => simp [evaluate, conditionRun, fixClock, Nat.min_eq_right bound]
      | raise value => exact False.elim (noRaise value rfl)
    | val values =>
      obtain ⟨value, rfl⟩ := BvlSem.evaluate_singleton condition env state next values conditionRun
      cases boolRun : asBool value with
      | none => simp [evaluate, conditionRun, fixClock, Nat.min_eq_right bound, boolRun]
      | some choice =>
        cases choice with
        | false =>
          have branchBound := evaluate_clock_le [no] env next
          have overallBound : (evaluate [no] env next).2.clock ≤ state.clock := by omega
          simp [evaluate, conditionRun, fixClock, Nat.min_eq_right bound,
            Nat.min_eq_right branchBound, Nat.min_eq_right overallBound, boolRun]
        | true =>
          have branchBound := evaluate_clock_le [yes] env next
          have overallBound : (evaluate [yes] env next).2.clock ≤ state.clock := by omega
          simp [evaluate, conditionRun, fixClock, Nat.min_eq_right bound,
            Nat.min_eq_right branchBound, Nat.min_eq_right overallBound, boolRun]

/-- Evaluation of a conditional respects equality of its test and branches. -/
theorem evaluate_if_congr {C F : Type} (condition condition' yes yes' no no' : Bvl.Exp)
    (env : List Value) (state : State C F)
    (conditionEq : evaluate [condition] env state = evaluate [condition'] env state)
    (yesEq : ∀ next : State C F, evaluate [yes] env next = evaluate [yes'] env next)
    (noEq : ∀ next : State C F, evaluate [no] env next = evaluate [no'] env next) :
    evaluate [.ifThenElse condition yes no] env state = evaluate [.ifThenElse condition' yes' no'] env state := by
  rw [evaluate, fixClock_evaluate, evaluate, fixClock_evaluate, conditionEq]
  repeat' split <;> simp_all

/-- The conditional branch of `makeHandle` preserves evaluation, including
selectively pushing the handler into the only potentially raising branch. -/
theorem evaluate_makeHandle_if {C F : Type} (condition yes no handler : Bvl.Exp) (depth : Nat)
    (env : List Value) (state : State C F) (bound : depth ≤ env.length)
    (conditionIH : ∀ (env : List Value) (state : State C F),
      evaluate [handleSimp condition] env state = evaluate [condition] env state)
    (yesIH : ∀ (env : List Value) (state : State C F),
      evaluate [handleSimp yes] env state = evaluate [yes] env state)
    (noIH : ∀ (env : List Value) (state : State C F),
      evaluate [handleSimp no] env state = evaluate [no] env state)
    (handlerIH : ∀ (env : List Value) (state : State C F),
      evaluate [handleSimp handler] env state = evaluate [handler] env state)
    (yesMakeIH : ∀ (next : State C F), evaluate [makeHandle yes handler depth] env next =
      evaluate [.handle yes (handleAdjVars 1 depth handler)] env next)
    (noMakeIH : ∀ (next : State C F), evaluate [makeHandle no handler depth] env next =
      evaluate [.handle no (handleAdjVars 1 depth handler)] env next) :
    evaluate [makeHandle (.ifThenElse condition yes no) handler depth] env state =
      evaluate [.handle (.ifThenElse condition yes no) (handleAdjVars 1 depth handler)] env state := by
  have adjusted : ∀ (value : Value) (next : State C F),
      evaluate [handleAdjVars 1 depth (handleSimp handler)] (value :: env) next =
        evaluate [handleAdjVars 1 depth handler] (value :: env) next := by
    intro value next
    apply handleAdjVars_evaluate_congr _ _ 1 depth (value :: env) next
    · exact fun env => handlerIH env next
    · simp only [List.length_cons]; omega
  have conditionSame : ∀ next : State C F,
      evaluate [handleSimp (.ifThenElse condition yes no)] env next =
        evaluate [.ifThenElse condition yes no] env next := by
    intro next
    simp only [handleSimp]
    exact evaluate_if_congr _ _ _ _ _ _ env next (conditionIH env next) (yesIH env) (noIH env)
  have fallback : evaluate [.handle (handleSimp (.ifThenElse condition yes no))
      (handleAdjVars 1 depth (handleSimp handler))] env state =
      evaluate [.handle (.ifThenElse condition yes no) (handleAdjVars 1 depth handler)] env state := by
    simp only [evaluate, conditionSame]
    repeat' split <;> simp_all
  cases hc : canRaise condition with
  | true => simpa [makeHandle, hc] using fallback
  | false =>
    cases hy : canRaise yes <;> cases hn : canRaise no
    · simpa [makeHandle, hc, hy, hn] using fallback
    · rw [evaluate_handle_if_push condition yes no (handleAdjVars 1 depth handler) env state hc]
      simp only [makeHandle, hc, hy, hn, Bool.false_eq_true, ↓reduceIte]
      apply evaluate_if_congr _ _ _ _ _ _ env state (conditionIH env state)
      · intro next
        exact (yesIH env next).trans (evaluate_handle_of_noRaise yes _ env next hy).symm
      · exact noMakeIH
    · rw [evaluate_handle_if_push condition yes no (handleAdjVars 1 depth handler) env state hc]
      simp only [makeHandle, hc, hy, hn, Bool.false_eq_true, ↓reduceIte]
      apply evaluate_if_congr _ _ _ _ _ _ env state (conditionIH env state)
      · exact yesMakeIH
      · intro next
        exact (noIH env next).trans (evaluate_handle_of_noRaise no _ env next hn).symm
    · simpa [makeHandle, hc, hy, hn] using fallback
end Flapjack.Compiler.Backend.BvlHandle.Proofs
