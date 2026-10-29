import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClockShift

/-! Clock-extension cases for proof-side closure application. Evaluator and
state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Closure application preserves non-timeout results under clock extension,
assuming the called body and subsequent application induction hypotheses. -/
theorem evaluateApp_addClock_step {C F : Type} (location : Option Nat) (function : Value)
    (args : List Value) (state next : State C F) (result : Result (List Value) Value) (extra : Nat)
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List Value) (bodyState bodyNext : State C F)
      (bodyResult : Result (List Value) Value), bodyState.clock < state.clock →
      evaluate [body] env bodyState = (bodyResult, bodyNext) → bodyResult ≠ .err (.abort .timeoutError) →
      evaluate [body] env { bodyState with clock := bodyState.clock + extra } =
        (bodyResult, { bodyNext with clock := bodyNext.clock + extra }))
    (appIH : ∀ (value : Value) (rest : List Value) (appState appNext : State C F)
      (appResult : Result (List Value) Value), appState.clock < state.clock →
      evaluateApp location value rest appState = (appResult, appNext) → appResult ≠ .err (.abort .timeoutError) →
      evaluateApp location value rest { appState with clock := appState.clock + extra } =
        (appResult, { appNext with clock := appNext.clock + extra }))
    (run : evaluateApp location function args state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluateApp location function args { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases args with
  | nil =>
    simp [evaluateApp] at run ⊢
    rcases run with ⟨rfl, rfl⟩
    simp
  | cons first rest =>
    rw [evaluateApp] at run ⊢
    cases found : destClosure state.maxApp location function (first :: rest) with
    | none =>
      rw [found] at run
      simp at run ⊢
      rcases run with ⟨rfl, rfl⟩
      simp
    | some kind =>
      rw [found] at run
      dsimp only at run ⊢
      cases kind with
      | partialApp value =>
        dsimp only at run ⊢
        by_cases timeout : state.clock < (first :: rest).length
        · rw [if_pos timeout] at run
          simp at run
          exact (notTimeout run.1.symm).elim
        · have enough : (first :: rest).length ≤ state.clock := by omega
          have shiftedEnough : ¬ state.clock + extra < (first :: rest).length := by omega
          rw [if_neg timeout] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          rw [if_neg shiftedEnough]
          simp only [decClock]
          simp only [List.length_cons] at enough ⊢
          congr 1
          congr 1
          omega
      | fullApp body bodyEnv remaining =>
        dsimp only at run ⊢
        have smallerArgs := destClosure_full_remaining_lt state.maxApp location function (first :: rest)
          bodyEnv remaining body found
        let cost := (first :: rest).length - remaining.length
        have positive : 0 < cost := Nat.sub_pos_of_lt smallerArgs
        by_cases timeout : state.clock < cost
        · rw [if_pos timeout] at run
          simp at run
          exact (notTimeout run.1.symm).elim
        · have enough : cost ≤ state.clock := by omega
          have shiftedEnough : ¬ state.clock + extra < cost := by omega
          have smaller : (decClock cost state).clock < state.clock := by simp [decClock]; omega
          have clocks : decClock cost { state with clock := state.clock + extra } =
              { decClock cost state with clock := (decClock cost state).clock + extra } := by
            simp only [decClock]
            congr 1
            omega
          rw [if_neg timeout] at run
          rw [if_neg shiftedEnough]
          rw [clocks, fixClock_evaluate]
          rw [fixClock_evaluate] at run
          cases bodyRun : evaluate [body] bodyEnv (decClock cost state) with
          | mk bodyResult bodyNext =>
            have bodyBound : bodyNext.clock ≤ (decClock cost state).clock := by
              have bound := evaluate_clock_le [body] bodyEnv (decClock cost state)
              simpa [bodyRun] using bound
            rw [bodyRun] at run
            have bodyNotTimeout : bodyResult ≠ .err (.abort .timeoutError) := by
              intro bad
              subst bodyResult
              simp at run
              exact notTimeout run.1.symm
            have shiftedBody := bodyIH body bodyEnv (decClock cost state) bodyNext bodyResult smaller bodyRun bodyNotTimeout
            rw [shiftedBody]
            cases bodyResult with
            | err error => simp_all
            | val values =>
              cases values with
              | nil => simp_all
              | cons value tail =>
                cases tail with
                | nil =>
                  dsimp only at run ⊢
                  have nextSmaller : bodyNext.clock < state.clock := by omega
                  exact appIH value remaining bodyNext next result nextSmaller run notTimeout
                | cons other tail => simp_all


/-- Application-expression case of clock extension, assuming argument,
function, and closure-application cases. -/
theorem evaluate_app_addClock {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List Value) (state next : State C F)
    (result : Result (List Value) Value) (extra : Nat)
    (argsIH : ∀ (argResult : Result (List Value) Value) (argNext : State C F),
      evaluate args env state = (argResult, argNext) → argResult ≠ .err (.abort .timeoutError) →
      evaluate args env { state with clock := state.clock + extra } =
        (argResult, { argNext with clock := argNext.clock + extra }))
    (functionIH : ∀ (argNext functionNext : State C F) (functionResult : Result (List Value) Value),
      argNext.clock ≤ state.clock → evaluate [function] env argNext = (functionResult, functionNext) →
      functionResult ≠ .err (.abort .timeoutError) →
      evaluate [function] env { argNext with clock := argNext.clock + extra } =
        (functionResult, { functionNext with clock := functionNext.clock + extra }))
    (appIH : ∀ (value : Value) (values : List Value) (functionNext final : State C F)
      (appResult : Result (List Value) Value), functionNext.clock ≤ state.clock →
      evaluateApp location value values functionNext = (appResult, final) →
      appResult ≠ .err (.abort .timeoutError) →
      evaluateApp location value values { functionNext with clock := functionNext.clock + extra } =
        (appResult, { final with clock := final.clock + extra }))
    (run : evaluate [.app trace location function args] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.app trace location function args] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases args with
  | nil =>
    simp [evaluate] at run ⊢
    rcases run with ⟨rfl, rfl⟩
    simp
  | cons first rest =>
    cases argsRun : evaluate (first :: rest) env state with
    | mk argsResult argsNext =>
      have argsBound : argsNext.clock ≤ state.clock := by
        have bound := evaluate_clock_le (first :: rest) env state
        simpa [argsRun] using bound
      rw [evaluate, fixClock_evaluate, argsRun] at run
      have argsNotTimeout : argsResult ≠ .err (.abort .timeoutError) := by
        intro bad
        subst argsResult
        simp at run
        exact notTimeout run.1.symm
      have shiftedArgs := argsIH argsResult argsNext argsRun argsNotTimeout
      rw [evaluate, fixClock_evaluate, shiftedArgs]
      cases argsResult with
      | err error => simp_all
      | val values =>
        cases functionRun : evaluate [function] env argsNext with
        | mk functionResult functionNext =>
          have functionBound : functionNext.clock ≤ state.clock := by
            have bound := evaluate_clock_le [function] env argsNext
            simp only [functionRun] at bound
            omega
          dsimp only at run ⊢
          rw [fixClock_evaluate, functionRun] at run
          have functionNotTimeout : functionResult ≠ .err (.abort .timeoutError) := by
            intro bad
            subst functionResult
            simp at run
            exact notTimeout run.1.symm
          have shiftedFunction := functionIH argsNext functionNext functionResult argsBound functionRun functionNotTimeout
          rw [fixClock_evaluate, shiftedFunction]
          cases functionResult with
          | err error => simp_all
          | val functionValues =>
            change evaluateApp location (@Flapjack.holHd Value ⟨unitValue⟩ functionValues) values functionNext =
              (result, next) at run
            change evaluateApp location (@Flapjack.holHd Value ⟨unitValue⟩ functionValues) values
              { functionNext with clock := functionNext.clock + extra } = _
            exact appIH _ values functionNext next result functionBound run notTimeout


/-- Forced-thunk case of clock extension, assuming the argument and thunk
application cases. -/
theorem evaluate_force_addClock {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (state next : State C F)
    (result : Result (List Value) Value) (extra : Nat)
    (argsIH : ∀ (argResult : Result (List Value) Value) (argNext : State C F),
      evaluate args env state = (argResult, argNext) → argResult ≠ .err (.abort .timeoutError) →
      evaluate args env { state with clock := state.clock + extra } =
        (argResult, { argNext with clock := argNext.clock + extra }))
    (forceIH : ∀ (value : Value) (argNext final : State C F) (forceResult : Result (List Value) Value),
      argNext.clock ≤ state.clock → evaluate [appUnit (.var .none 0)] [value] argNext = (forceResult, final) →
      forceResult ≠ .err (.abort .timeoutError) →
      evaluate [appUnit (.var .none 0)] [value] { argNext with clock := argNext.clock + extra } =
        (forceResult, { final with clock := final.clock + extra }))
    (run : evaluate [.op trace (.thunkOp .forceThunk) args] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.op trace (.thunkOp .forceThunk) args] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases argsRun : evaluate args env state with
  | mk argResult argNext =>
    have bound : argNext.clock ≤ state.clock := by
      have clock := evaluate_clock_le args env state
      simpa [argsRun] using clock
    rw [evaluate, fixClock_evaluate, argsRun] at run
    have argNotTimeout : argResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst argResult
      simp at run
      exact notTimeout run.1.symm
    have shiftedArgs := argsIH argResult argNext argsRun argNotTimeout
    rw [evaluate, fixClock_evaluate, shiftedArgs]
    cases argResult with
    | err error => simp_all
    | val values =>
      dsimp only at run ⊢
      cases inspected : destThunk values argNext.refs with
      | badRef | notThunk =>
        simp [inspected] at run ⊢
        rcases run with ⟨rfl, rfl⟩
        simp
      | isThunk mode value =>
        cases mode with
        | evaluated =>
          simp [inspected] at run ⊢
          rcases run with ⟨rfl, rfl⟩
          simp
        | notEvaluated =>
          rw [inspected] at run
          dsimp only at run ⊢
          cases forceRun : evaluate [appUnit (.var .none 0)] [value] argNext with
          | mk forceResult final =>
            have forceNotTimeout : forceResult ≠ .err (.abort .timeoutError) := by
              intro bad
              subst forceResult
              simp [forceRun] at run
              exact notTimeout run.1.symm
            have shiftedForce := forceIH value argNext final forceResult bound forceRun forceNotTimeout
            rw [forceRun] at run
            rw [shiftedForce]
            cases forceResult with
            | err error => simp_all
            | val forced =>
              dsimp only at run ⊢
              cases updated : updateThunk values final.refs forced with
              | none =>
                simp [updated] at run ⊢
                rcases run with ⟨rfl, rfl⟩
                simp
              | some refs =>
                simp [updated] at run ⊢
                rcases run with ⟨rfl, rfl⟩
                simp


/-- Non-timeout closure evaluation and application are stable under extra
clock. The evaluator and state carriers remain pending HOL correspondence review. -/
theorem evaluate_addClock {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List Value) (state next : State C F)
      (result : Result (List Value) Value) (extra : Nat),
      evaluate expressions env state = (result, next) → result ≠ .err (.abort .timeoutError) →
      evaluate expressions env { state with clock := state.clock + extra } =
        (result, { next with clock := next.clock + extra })) ∧
    (∀ (location : Option Nat) (function : Value) (args : List Value) (state next : State C F)
      (result : Result (List Value) Value) (extra : Nat),
      evaluateApp location function args state = (result, next) → result ≠ .err (.abort .timeoutError) →
      evaluateApp location function args { state with clock := state.clock + extra } =
        (result, { next with clock := next.clock + extra })) := by
  have all : ∀ clock : Nat,
      (∀ (location : Option Nat) (function : Value) (args : List Value) (state next : State C F)
        (result : Result (List Value) Value) (extra : Nat), state.clock = clock →
        evaluateApp location function args state = (result, next) → result ≠ .err (.abort .timeoutError) →
        evaluateApp location function args { state with clock := state.clock + extra } =
          (result, { next with clock := next.clock + extra })) ∧
      (∀ (weight : Nat) (expressions : List ClosLang.Exp) (env : List Value) (state next : State C F)
        (result : Result (List Value) Value) (extra : Nat), state.clock = clock → expsWeight expressions = weight →
        evaluate expressions env state = (result, next) → result ≠ .err (.abort .timeoutError) →
        evaluate expressions env { state with clock := state.clock + extra } =
          (result, { next with clock := next.clock + extra })) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ (location : Option Nat) (function : Value) (args : List Value) (state next : State C F)
          (result : Result (List Value) Value) (extra : Nat), state.clock = clock →
          evaluateApp location function args state = (result, next) → result ≠ .err (.abort .timeoutError) →
          evaluateApp location function args { state with clock := state.clock + extra } =
            (result, { next with clock := next.clock + extra }) := by
        intro location function args state next result extra stateClock run notTimeout
        apply evaluateApp_addClock_step location function args state next result extra ?_ ?_ run notTimeout
        · intro body env bodyState bodyNext bodyResult smaller bodyRun bodyNotTimeout
          exact (clockIH bodyState.clock (by omega)).2 (expsWeight [body]) [body] env bodyState bodyNext bodyResult extra rfl rfl bodyRun bodyNotTimeout
        · intro value rest appState appNext appResult smaller appRun appNotTimeout
          exact (clockIH appState.clock (by omega)).1 location value rest appState appNext appResult extra rfl appRun appNotTimeout
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ (expressions : List ClosLang.Exp) (env : List Value) (state next : State C F)
              (result : Result (List Value) Value) (extra : Nat), state.clock ≤ clock → expsWeight expressions < weight →
              evaluate expressions env state = (result, next) → result ≠ .err (.abort .timeoutError) →
              evaluate expressions env { state with clock := state.clock + extra } =
                (result, { next with clock := next.clock + extra }) := by
            intro expressions env state next result extra clockLe weightLt run notTimeout
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions env state next result extra rfl rfl run notTimeout
            · exact weightIH (expsWeight expressions) weightLt expressions env state next result extra clockEq rfl run notTimeout
          have smaller : ∀ (expressions : List ClosLang.Exp) (env : List Value) (state next : State C F)
              (result : Result (List Value) Value) (extra : Nat), state.clock < clock →
              evaluate expressions env state = (result, next) → result ≠ .err (.abort .timeoutError) →
              evaluate expressions env { state with clock := state.clock + extra } =
                (result, { next with clock := next.clock + extra }) := by
            intro expressions env state next result extra clockLt run notTimeout
            exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions env state next result extra rfl rfl run notTimeout
          have appBound : ∀ (location : Option Nat) (function : Value) (args : List Value) (state next : State C F)
              (result : Result (List Value) Value) (extra : Nat), state.clock ≤ clock →
              evaluateApp location function args state = (result, next) → result ≠ .err (.abort .timeoutError) →
              evaluateApp location function args { state with clock := state.clock + extra } =
                (result, { next with clock := next.clock + extra }) := by
            intro location function args state next result extra clockLe run notTimeout
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).1 location function args state next result extra rfl run notTimeout
            · exact appAll location function args state next result extra clockEq run notTimeout
          intro expressions env state next result extra stateClock measure run notTimeout
          cases expressions with
          | nil =>
            simp [evaluate] at run ⊢
            rcases run with ⟨rfl, rfl⟩
            simp
          | cons first rest =>
            cases rest with
            | cons second tail =>
              apply evaluate_list_addClock first second tail env state next result extra ?_ ?_ run notTimeout
              · intro headResult headNext headRun headNotTimeout
                apply exprIH [first] env state headNext headResult extra (by omega) ?_ headRun headNotTimeout
                simp only [expsWeight] at measure ⊢
                omega
              · intro headNext tailNext tailResult bound tailRun tailNotTimeout
                apply exprIH (second :: tail) env headNext tailNext tailResult extra (by omega) ?_ tailRun tailNotTimeout
                simp only [expsWeight] at measure ⊢
                omega
            | nil =>
              cases first with
              | var trace index => exact evaluate_var_addClock trace index env state next result extra run
              | fn name location selected arity body => exact evaluate_fn_addClock name location selected arity body env state next result extra run
              | raise trace body =>
                apply evaluate_raise_addClock trace body env state next result extra ?_ run notTimeout
                intro childResult childNext childRun childNotTimeout
                apply exprIH [body] env state childNext childResult extra (by omega) ?_ childRun childNotTimeout
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              | tick trace body =>
                apply evaluate_tick_addClock trace body env state next result extra ?_ run notTimeout
                intro childResult childNext childRun childNotTimeout
                by_cases zero : state.clock = 0
                · apply exprIH [body] env (decClock 1 state) childNext childResult extra (by simp [decClock]; omega) ?_ childRun childNotTimeout
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
                · apply smaller [body] env (decClock 1 state) childNext childResult extra ?_ childRun childNotTimeout
                  simp [decClock]
                  omega
              | call trace ticks location args =>
                apply evaluate_call_addClock trace ticks location args env state next result extra ?_ ?_ run notTimeout
                · intro argResult argNext argRun argNotTimeout
                  apply exprIH args env state argNext argResult extra (by omega) ?_ argRun argNotTimeout
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
                · intro body values bodyState bodyNext bodyResult smallerClock bodyRun bodyNotTimeout
                  exact smaller [body] values bodyState bodyNext bodyResult extra (by omega) bodyRun bodyNotTimeout
              | «let» trace bindings body =>
                apply evaluate_let_addClock trace bindings body env state next result extra ?_ ?_ run notTimeout
                · intro bindingResult bindingNext bindingRun bindingNotTimeout
                  apply exprIH bindings env state bindingNext bindingResult extra (by omega) ?_ bindingRun bindingNotTimeout
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
                · intro values bindingNext final bodyResult bound bodyRun bodyNotTimeout
                  apply exprIH [body] (values ++ env) bindingNext final bodyResult extra (by omega) ?_ bodyRun bodyNotTimeout
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
              | letrec names location selected functions body =>
                apply evaluate_letrec_addClock names location selected functions body env state next result extra ?_ run
                intro newEnv bodyRun
                apply exprIH [body] newEnv state next result extra (by omega) ?_ bodyRun notTimeout
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              | handle trace body handler =>
                apply evaluate_handle_addClock trace body handler env state next result extra ?_ ?_ run notTimeout
                · intro bodyResult bodyNext bodyRun bodyNotTimeout
                  apply exprIH [body] env state bodyNext bodyResult extra (by omega) ?_ bodyRun bodyNotTimeout
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
                · intro value bodyNext final handlerResult bound handlerRun handlerNotTimeout
                  apply exprIH [handler] (value :: env) bodyNext final handlerResult extra (by omega) ?_ handlerRun handlerNotTimeout
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
              | ifThenElse trace condition yes no =>
                apply evaluate_if_addClock trace condition yes no env state next result extra ?_ ?_ run notTimeout
                · intro conditionResult conditionNext conditionRun conditionNotTimeout
                  apply exprIH [condition] env state conditionNext conditionResult extra (by omega) ?_ conditionRun conditionNotTimeout
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
                · intro choice conditionNext final branchResult bound branchRun branchNotTimeout
                  cases choice with
                  | false =>
                    apply exprIH [no] env conditionNext final branchResult extra (by omega) ?_ branchRun branchNotTimeout
                    simp only [expsWeight, expWeight] at measure ⊢
                    omega
                  | true =>
                    apply exprIH [yes] env conditionNext final branchResult extra (by omega) ?_ branchRun branchNotTimeout
                    simp only [expsWeight, expWeight] at measure ⊢
                    omega
              | app trace location function args =>
                apply evaluate_app_addClock trace location function args env state next result extra ?_ ?_ ?_ run notTimeout
                · intro argResult argNext argRun argNotTimeout
                  apply exprIH args env state argNext argResult extra (by omega) ?_ argRun argNotTimeout
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
                · intro argNext functionNext functionResult bound functionRun functionNotTimeout
                  apply exprIH [function] env argNext functionNext functionResult extra (by omega) ?_ functionRun functionNotTimeout
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
                · intro value values functionNext final appResult bound appRun appNotTimeout
                  exact appBound location value values functionNext final appResult extra (by omega) appRun appNotTimeout
              | op trace op args =>
                have argsSmaller : expsWeight args < weight := by
                  have bound := opWeight_gt trace op args
                  simp only [expsWeight] at measure
                  omega
                have ordinary : ∀ op, op ≠ .install → op ≠ .thunkOp .forceThunk →
                    evaluate [.op trace op args] env state = (result, next) →
                    evaluate [.op trace op args] env { state with clock := state.clock + extra } =
                      (result, { next with clock := next.clock + extra }) := by
                  intro op notInstall notForce opRun
                  apply evaluate_ordinaryOp_addClock trace op args env state next result extra notInstall notForce ?_ opRun notTimeout
                  intro argResult argNext argRun argNotTimeout
                  apply exprIH args env state argNext argResult extra (by omega) ?_ argRun argNotTimeout
                  exact argsSmaller
                cases op with
                | install =>
                  apply evaluate_install_addClock trace args env state next result extra ?_ ?_ run notTimeout
                  · intro argResult argNext argRun argNotTimeout
                    apply exprIH args env state argNext argResult extra (by omega) ?_ argRun argNotTimeout
                    simp only [expsWeight, expWeight] at measure ⊢
                    omega
                  · intro program installed final programResult bound programRun programNotTimeout
                    exact smaller program [] installed final programResult extra (by omega) programRun programNotTimeout
                | thunkOp operation =>
                  cases operation with
                  | forceThunk =>
                    apply evaluate_force_addClock trace args env state next result extra ?_ ?_ run notTimeout
                    · intro argResult argNext argRun argNotTimeout
                      apply exprIH args env state argNext argResult extra (by omega) ?_ argRun argNotTimeout
                      simp only [expsWeight, expWeight] at measure ⊢
                      omega
                    · intro value argNext final forceResult bound forceRun forceNotTimeout
                      change evaluate [.app .none none (.var .none 0) [.op .none (.blockOp (.cons 0)) []]] [value] argNext = (forceResult, final) at forceRun
                      change evaluate [.app .none none (.var .none 0) [.op .none (.blockOp (.cons 0)) []]] [value]
                        { argNext with clock := argNext.clock + extra } = (forceResult, { final with clock := final.clock + extra })
                      apply evaluate_app_addClock .none none (.var .none 0) [.op .none (.blockOp (.cons 0)) []]
                        [value] argNext final forceResult extra ?_ ?_ ?_ forceRun forceNotTimeout
                      · intro argResult argState argRun _
                        simp [evaluate, fixClock, doApp, applyBlock] at argRun ⊢
                        rcases argRun with ⟨rfl, rfl⟩
                        simp
                      · intro argState fnState fnResult _ fnRun _
                        exact evaluate_var_addClock .none 0 [value] argState fnState fnResult extra fnRun
                      · intro fnValue values fnState appNext appResult appLe appRun appNotTimeout
                        exact appBound none fnValue values fnState appNext appResult extra (by omega) appRun appNotTimeout
                  | allocThunk mode => exact ordinary _ (by simp) (by simp) run
                  | updateThunk mode => exact ordinary _ (by simp) (by simp) run
                | label _ | ffi _ | intOp _ | wordOp _ | blockOp _ | globOp _ | memOp _ =>
                  exact ordinary _ (by simp) (by simp) run
  constructor
  · intro expressions env state next result extra run notTimeout
    exact (all state.clock).2 (expsWeight expressions) expressions env state next result extra rfl rfl run notTimeout
  · intro location function args state next result extra run notTimeout
    exact (all state.clock).1 location function args state next result extra rfl run notTimeout

end Flapjack.Compiler.Backend.ClosSem
