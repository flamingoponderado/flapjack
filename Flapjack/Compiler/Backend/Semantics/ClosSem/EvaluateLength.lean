import Flapjack.Compiler.Backend.Semantics.ClosSem.AppClockShift

/-! Successful-result length for the proof-side closure evaluator. The
evaluator and state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- A successful closure application returns one value, assuming the
called-body and subsequent-application cases at smaller clocks. -/
theorem evaluateApp_length_step {C F : Type} (location : Option Nat) (function : Value)
    (args : List Value) (state next : State C F) (values : List Value)
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List Value) (bodyState bodyNext : State C F)
      (bodyValues : List Value), bodyState.clock < state.clock →
      evaluate [body] env bodyState = (.val bodyValues, bodyNext) → bodyValues.length = 1)
    (appIH : ∀ (value : Value) (rest : List Value) (appState appNext : State C F)
      (appValues : List Value), appState.clock < state.clock →
      evaluateApp location value rest appState = (.val appValues, appNext) → appValues.length = 1)
    (run : evaluateApp location function args state = (.val values, next)) : values.length = 1 := by
  cases args with
  | nil =>
    simp [evaluateApp] at run
    rcases run with ⟨rfl, _⟩
    rfl
  | cons first rest =>
    rw [evaluateApp] at run
    cases found : destClosure state.maxApp location function (first :: rest) with
    | none => rw [found] at run; simp at run
    | some kind =>
      rw [found] at run
      dsimp only at run
      cases kind with
      | partialApp value =>
        dsimp only at run
        split at run
        · simp at run
        · simp at run
          rcases run with ⟨rfl, _⟩
          rfl
      | fullApp body bodyEnv remaining =>
        dsimp only at run
        have remainingLt := destClosure_full_remaining_lt state.maxApp location function (first :: rest)
          bodyEnv remaining body found
        let cost := (first :: rest).length - remaining.length
        have costPositive : 0 < cost := Nat.sub_pos_of_lt remainingLt
        split at run
        · simp at run
        · rename_i enough
          rw [fixClock_evaluate] at run
          cases bodyRun : evaluate [body] bodyEnv (decClock cost state) with
          | mk bodyResult bodyNext =>
            have bodyBound : bodyNext.clock ≤ (decClock cost state).clock := by
              have bound := evaluate_clock_le [body] bodyEnv (decClock cost state)
              simpa [bodyRun] using bound
            have smaller : (decClock cost state).clock < state.clock := by simp [decClock]; omega
            rw [bodyRun] at run
            cases bodyResult with
            | err error => simp at run
            | val bodyValues =>
              have singleton := bodyIH body bodyEnv (decClock cost state) bodyNext bodyValues smaller bodyRun
              cases bodyValues with
              | nil => simp at singleton
              | cons value tail =>
                cases tail with
                | nil =>
                  dsimp only at run
                  exact appIH value remaining bodyNext next values (by omega) run
                | cons other tail => simp at singleton


/-- If every successful singleton evaluation returns one value, successful
list evaluation returns one value per expression. This isolates the list
sequencing case needed by the mutual length argument. -/
theorem evaluate_list_length_of_singletons {C F : Type}
    (singleton : ∀ (expression : ClosLang.Exp) (env : List Value)
      (state next : State C F) (values : List Value),
      evaluate [expression] env state = (.val values, next) → values.length = 1)
    (expressions : List ClosLang.Exp) (env : List Value) (state next : State C F)
    (values : List Value)
    (run : evaluate expressions env state = (.val values, next)) :
    values.length = expressions.length := by
  induction expressions generalizing state next values with
  | nil => simp [evaluate] at run; rcases run with ⟨rfl, _⟩; rfl
  | cons first rest ih =>
    cases rest with
    | nil => simpa using singleton first env state next values run
    | cons second tail =>
      rw [evaluate, fixClock_evaluate] at run
      cases headRun : evaluate [first] env state with
      | mk headResult headNext =>
        rw [headRun] at run
        cases headResult with
        | err error => simp at run
        | val headValues =>
          cases tailRun : evaluate (second :: tail) env headNext with
          | mk tailResult tailNext =>
            rw [tailRun] at run
            cases tailResult with
            | err error => simp at run
            | val tailValues =>
              simp at run
              rcases run with ⟨rfl, _⟩
              have tailLength := ih headNext tailNext tailValues tailRun
              simpa using congrArg Nat.succ tailLength

end Flapjack.Compiler.Backend.ClosSem
