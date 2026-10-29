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

/-- Ordinary primitive operations produce exactly one value on success. -/
theorem evaluate_ordinaryOp_length {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List Value)
    (state next : State C F) (values : List Value)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (run : evaluate [.op trace op args] env state = (.val values, next)) :
    values.length = 1 := by
  rw [evaluate_ordinaryOp_eq trace op args env state notInstall notForce] at run
  cases argsRun : evaluate args env state with
  | mk result last =>
    rw [argsRun] at run
    cases result with
    | err error => simp at run
    | val arguments =>
      cases appRun : doApp op arguments.reverse last with
      | err error => simp [appRun] at run
      | val pair =>
        rcases pair with ⟨value, final⟩
        simp [appRun] at run
        rcases run with ⟨rfl, _⟩
        rfl

/-- Installation produces one value whenever the installed program succeeds. -/
theorem evaluate_install_length {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (state next : State C F)
    (values : List Value)
    (run : evaluate [.op trace .install args] env state = (.val values, next)) :
    values.length = 1 := by
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env state with
  | mk result last =>
    rw [argsRun] at run
    cases result with
    | err error => simp at run
    | val arguments =>
      dsimp only at run
      cases installRun : doInstall arguments.reverse last with
      | mk installResult installedState =>
        rw [installRun] at run
        cases installResult with
        | err error => simp at run
        | val program =>
          dsimp only at run
          cases programRun : evaluate program [] installedState with
          | mk programResult final =>
            rw [programRun] at run
            cases programResult with
            | err error => simp at run
            | val programValues =>
              simp at run
              rcases run with ⟨rfl, _⟩
              rfl

/-- The force-thunk case reduces its successful-result length to the
application used to evaluate an unevaluated thunk. -/
theorem evaluate_forceThunk_length_step {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (state next : State C F)
    (values : List Value)
    (forceIH : ∀ (value : Value) (argNext final : State C F) (forced : List Value),
      argNext.clock ≤ state.clock →
      evaluate [appUnit (.var .none 0)] [value] argNext = (.val forced, final) →
      forced.length = 1)
    (run : evaluate [.op trace (.thunkOp .forceThunk) args] env state = (.val values, next)) :
    values.length = 1 := by
  cases argsRun : evaluate args env state with
  | mk argResult argNext =>
    have bound : argNext.clock ≤ state.clock := by
      have clock := evaluate_clock_le args env state
      simpa [argsRun] using clock
    rw [evaluate, fixClock_evaluate, argsRun] at run
    cases argResult with
    | err error => simp at run
    | val arguments =>
      dsimp only at run
      cases inspected : destThunk arguments argNext.refs with
      | badRef | notThunk => simp [inspected] at run
      | isThunk mode value =>
        cases mode with
        | evaluated =>
          simp [inspected] at run
          rcases run with ⟨rfl, _⟩
          rfl
        | notEvaluated =>
          rw [inspected] at run
          dsimp only at run
          cases forceRun : evaluate [appUnit (.var .none 0)] [value] argNext with
          | mk forceResult final =>
            rw [forceRun] at run
            cases forceResult with
            | err error => simp at run
            | val forced =>
              dsimp only at run
              cases updated : updateThunk arguments final.refs forced with
              | none => simp [updated] at run
              | some refs =>
                simp [updated] at run
                rcases run with ⟨rfl, _⟩
                exact forceIH value argNext final forced bound forceRun

/-- Successful evaluation returns one value per expression, and successful
application returns one value. -/
theorem evaluate_length {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List Value) (state next : State C F) (values : List Value),
      evaluate expressions env state = (.val values, next) → values.length = expressions.length) ∧
    (∀ (location : Option Nat) (function : Value) (args : List Value) (state next : State C F) (values : List Value),
      evaluateApp location function args state = (.val values, next) → values.length = 1) := by
  have all : ∀ clock : Nat,
      (∀ (location : Option Nat) (function : Value) (args : List Value) (state next : State C F) (values : List Value),
        state.clock = clock → evaluateApp location function args state = (.val values, next) → values.length = 1) ∧
      (∀ (weight : Nat) (expressions : List ClosLang.Exp) (env : List Value) (state next : State C F) (values : List Value),
        state.clock = clock → expsWeight expressions = weight →
        evaluate expressions env state = (.val values, next) → values.length = expressions.length) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ (location : Option Nat) (function : Value) (args : List Value) (state next : State C F) (values : List Value),
          state.clock = clock → evaluateApp location function args state = (.val values, next) → values.length = 1 := by
        intro location function args state next values stateClock run
        apply evaluateApp_length_step location function args state next values ?_ ?_ run
        · intro body env bodyState bodyNext bodyValues smaller bodyRun
          have one := (clockIH bodyState.clock (by omega)).2 (expsWeight [body]) [body] env bodyState bodyNext bodyValues rfl rfl bodyRun
          simpa using one
        · intro value rest appState appNext appValues smaller appRun
          exact (clockIH appState.clock (by omega)).1 location value rest appState appNext appValues rfl appRun
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ (expressions : List ClosLang.Exp) (env : List Value) (state next : State C F) (values : List Value),
              state.clock ≤ clock → expsWeight expressions < weight →
              evaluate expressions env state = (.val values, next) → values.length = expressions.length := by
            intro expressions env state next values clockLe weightLt run
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions env state next values rfl rfl run
            · exact weightIH (expsWeight expressions) weightLt expressions env state next values clockEq rfl run
          have smaller : ∀ (expressions : List ClosLang.Exp) (env : List Value) (state next : State C F) (values : List Value),
              state.clock < clock → evaluate expressions env state = (.val values, next) → values.length = expressions.length := by
            intro expressions env state next values clockLt run
            exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions env state next values rfl rfl run
          have appBound : ∀ (location : Option Nat) (function : Value) (args : List Value) (state next : State C F) (values : List Value),
              state.clock ≤ clock → evaluateApp location function args state = (.val values, next) → values.length = 1 := by
            intro location function args state next values clockLe run
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).1 location function args state next values rfl run
            · exact appAll location function args state next values clockEq run
          intro expressions env state next values stateClock measure run
          cases expressions with
          | nil => simp [evaluate] at run; rcases run with ⟨rfl, _⟩; rfl
          | cons first rest =>
            cases rest with
            | cons second tail =>
              have headBound := evaluate_clock_le [first] env state
              rw [evaluate, fixClock_evaluate] at run
              cases headRun : evaluate [first] env state with
              | mk headResult headNext =>
                simp only [headRun] at run headBound
                cases headResult with
                | err error => simp at run
                | val headValues =>
                  cases tailRun : evaluate (second :: tail) env headNext with
                  | mk tailResult tailNext =>
                    simp only [tailRun] at run
                    cases tailResult with
                    | err error => simp at run
                    | val tailValues =>
                      simp at run
                      rcases run with ⟨rfl, _⟩
                      have tailLength := exprIH (second :: tail) env headNext tailNext tailValues (by omega) (by
                        simp only [expsWeight] at measure ⊢; omega) tailRun
                      simpa using congrArg Nat.succ tailLength
            | nil =>
              cases first with
              | var trace index =>
                simp [evaluate] at run
                split at run <;> simp_all
                rcases run with ⟨rfl, _⟩
                rfl
              | fn name location selected arity body =>
                rw [evaluate.eq_def] at run
                dsimp only at run
                repeat' split at run <;> simp_all
                all_goals aesop
              | raise trace body =>
                rw [evaluate] at run
                cases bodyRun : evaluate [body] env state with
                | mk bodyResult bodyNext =>
                  rw [bodyRun] at run
                  cases bodyResult <;> simp at run
              | tick trace body =>
                rw [evaluate] at run
                split at run
                · simp at run
                · have bodyRun : evaluate [body] env (decClock 1 state) = (.val values, next) := run
                  by_cases zero : state.clock = 0
                  · apply exprIH [body] env (decClock 1 state) next values (by simp [decClock]; omega) ?_ bodyRun
                    simp only [expsWeight, expWeight] at measure ⊢
                    omega
                  · have one := smaller [body] env (decClock 1 state) next values (by simp [decClock]; omega) bodyRun
                    simpa using one
              | op trace op args =>
                cases op with
                | install => simpa using evaluate_install_length trace args env state next values run
                | thunkOp operation =>
                  cases operation with
                  | forceThunk =>
                    apply evaluate_forceThunk_length_step trace args env state next values ?_ run
                    intro value argNext final forced bound forceRun
                    have smallWeight : expsWeight [appUnit (.var .none 0)] < weight := by
                      have h := appUnit_var_weight
                      simp only [expsWeight, expWeight] at measure
                      simp only [appUnit, expsWeight, expWeight] at h ⊢
                      omega
                    have one := exprIH [appUnit (.var .none 0)] [value] argNext final forced (by omega) smallWeight forceRun
                    simpa using one
                  | allocThunk mode | updateThunk mode =>
                    exact evaluate_ordinaryOp_length trace _ args env state next values (by simp) (by simp) run
                | label | ffi | intOp | wordOp | blockOp | globOp | memOp =>
                  exact evaluate_ordinaryOp_length trace _ args env state next values (by simp) (by simp) run
              | «let» trace bindings body =>
                have bound := evaluate_clock_le bindings env state
                rw [evaluate, fixClock_evaluate] at run
                cases bindingRun : evaluate bindings env state with
                | mk result last =>
                  simp only [bindingRun] at run bound
                  cases result with
                  | err error => simp at run
                  | val bindingValues =>
                    have one := exprIH [body] (bindingValues ++ env) last next values (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢; omega) run
                    simpa using one
              | letrec names location selected functions body =>
                rw [evaluate.eq_def] at run
                dsimp only at run
                split at run
                · split at run
                  · simp at run
                  · have one := exprIH [body] _ state next values (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢; omega) run
                    simpa using one
                · simp at run
              | ifThenElse trace condition yes no =>
                have bound := evaluate_clock_le [condition] env state
                rw [evaluate, fixClock_evaluate] at run
                cases conditionRun : evaluate [condition] env state with
                | mk result last =>
                  simp only [conditionRun] at run bound
                  cases result with
                  | err error => simp at run
                  | val conditionValues =>
                    dsimp only at run
                    split at run
                    · simp at run
                    · have one := exprIH [yes] env last next values (by omega) (by
                        simp only [expsWeight, expWeight] at measure ⊢; omega) run
                      simpa using one
                    · have one := exprIH [no] env last next values (by omega) (by
                        simp only [expsWeight, expWeight] at measure ⊢; omega) run
                      simpa using one
              | handle trace body handler =>
                have bound := evaluate_clock_le [body] env state
                rw [evaluate, fixClock_evaluate] at run
                cases bodyRun : evaluate [body] env state with
                | mk result last =>
                  simp only [bodyRun] at run bound
                  cases result with
                  | val bodyValues =>
                    simp at run
                    rcases run with ⟨rfl, _⟩
                    have one := exprIH [body] env state last bodyValues (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢; omega) bodyRun
                    simpa using one
                  | err error =>
                    cases error with
                    | abort reason => simp at run
                    | raise value =>
                      have one := exprIH [handler] (value :: env) last next values (by omega) (by
                        simp only [expsWeight, expWeight] at measure ⊢; omega) run
                      simpa using one
              | call trace ticks location args =>
                have bound := evaluate_clock_le args env state
                rw [evaluate, fixClock_evaluate] at run
                cases argsRun : evaluate args env state with
                | mk result last =>
                  simp only [argsRun] at run bound
                  cases result with
                  | err error => simp at run
                  | val arguments =>
                    dsimp only at run
                    split at run
                    · simp at run
                    · rename_i selected body found
                      split at run
                      · simp at run
                      · have one := smaller [body] selected (decClock (ticks + 1) last) next values (by
                          simp only [decClock]; omega) run
                        simpa using one
              | app trace location function args =>
                cases args with
                | nil => simp [evaluate] at run
                | cons first rest =>
                  have argsBound := evaluate_clock_le (first :: rest) env state
                  rw [evaluate, fixClock_evaluate] at run
                  cases argsRun : evaluate (first :: rest) env state with
                  | mk argsResult argsNext =>
                    simp only [argsRun] at run argsBound
                    cases argsResult with
                    | err error => simp at run
                    | val arguments =>
                      dsimp only at run
                      rw [fixClock_evaluate] at run
                      have functionBound := evaluate_clock_le [function] env argsNext
                      cases functionRun : evaluate [function] env argsNext with
                      | mk functionResult functionNext =>
                        simp only [functionRun] at run functionBound
                        cases functionResult with
                        | err error => simp at run
                        | val functionValues =>
                          change evaluateApp location (@Flapjack.holHd Value ⟨unitValue⟩ functionValues)
                            arguments functionNext = (.val values, next) at run
                          exact appBound location _ arguments functionNext next values (by omega) run

  constructor
  · intro expressions env state next values run
    exact (all state.clock).2 (expsWeight expressions) expressions env state next values rfl rfl run
  · intro location function args state next values run
    exact (all state.clock).1 location function args state next values rfl run

/-- A successful singleton expression has a unique returned value. -/
theorem evaluate_singleton_value {C F : Type} (expression : ClosLang.Exp)
    (env : List Value) (state next : State C F) (values : List Value)
    (run : evaluate [expression] env state = (.val values, next)) :
    ∃ value, values = [value] := by
  have length := evaluate_length.1 [expression] env state next values run
  cases values with
  | nil => simp at length
  | cons value tail =>
    cases tail with
    | nil => exact ⟨value, rfl⟩
    | cons other tail => simp at length

end Flapjack.Compiler.Backend.ClosSem
