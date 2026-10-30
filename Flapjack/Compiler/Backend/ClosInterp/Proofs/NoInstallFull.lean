import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallControl

/-! Mutual no-install preservation for the proof-side closure evaluator.
The evaluator and its carriers await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Evaluation and application preserve no-install values and state. -/
theorem evaluate_noInstall {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
      (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosLang.hasInstallList expressions = false → valuesNoInstall env = true → evalStateNoInstall state →
      ClosSem.evaluate expressions env state = (result, next) → resultNoInstall result ∧ evalStateNoInstall next) ∧
    (∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
      (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      valueNoInstall function = true → valuesNoInstall args = true → evalStateNoInstall state →
      ClosSem.evaluateApp location function args state = (result, next) → resultNoInstall result ∧ evalStateNoInstall next) := by
  have all : ∀ clock : Nat,
      (∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
        (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
        state.clock = clock → valueNoInstall function = true → valuesNoInstall args = true → evalStateNoInstall state →
        ClosSem.evaluateApp location function args state = (result, next) → resultNoInstall result ∧ evalStateNoInstall next) ∧
      (∀ (weight : Nat) (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
        (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
        state.clock = clock → ClosSem.expsWeight expressions = weight → ClosLang.hasInstallList expressions = false →
        valuesNoInstall env = true → evalStateNoInstall state →
        ClosSem.evaluate expressions env state = (result, next) → resultNoInstall result ∧ evalStateNoInstall next) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
          (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
          state.clock = clock → valueNoInstall function = true → valuesNoInstall args = true → evalStateNoInstall state →
          ClosSem.evaluateApp location function args state = (result, next) → resultNoInstall result ∧ evalStateNoInstall next := by
        intro location function args state next result stateClock functionOk argsOk stateOk run
        apply evaluateApp_noInstall_step location function args state next result functionOk argsOk stateOk ?_ ?_ run
        · intro body env start final bodyResult smaller bodyOk envOk startOk bodyRun
          exact (clockIH start.clock (by omega)).2 (ClosSem.expsWeight [body]) [body] env start final bodyResult rfl rfl
            (by simp [ClosLang.hasInstallList, bodyOk]) envOk startOk bodyRun
        · intro value remaining start final appResult smaller valueOk remainingOk startOk appRun
          exact (clockIH start.clock (by omega)).1 location value remaining start final appResult rfl valueOk remainingOk startOk appRun
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
              (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
              state.clock ≤ clock → ClosSem.expsWeight expressions < weight → ClosLang.hasInstallList expressions = false →
              valuesNoInstall env = true → evalStateNoInstall state →
              ClosSem.evaluate expressions env state = (result, next) → resultNoInstall result ∧ evalStateNoInstall next := by
            intro expressions env state next result clockLe weightLt safe envOk stateOk run
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (ClosSem.expsWeight expressions) expressions env state next result rfl rfl safe envOk stateOk run
            · exact weightIH (ClosSem.expsWeight expressions) weightLt expressions env state next result clockEq rfl safe envOk stateOk run
          have smaller : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
              (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
              state.clock < clock → ClosLang.hasInstallList expressions = false → valuesNoInstall env = true → evalStateNoInstall state →
              ClosSem.evaluate expressions env state = (result, next) → resultNoInstall result ∧ evalStateNoInstall next := by
            intro expressions env state next result clockLt safe envOk stateOk run
            exact (clockIH state.clock clockLt).2 (ClosSem.expsWeight expressions) expressions env state next result rfl rfl safe envOk stateOk run
          have appBound : ∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
              (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
              state.clock ≤ clock → valueNoInstall function = true → valuesNoInstall args = true → evalStateNoInstall state →
              ClosSem.evaluateApp location function args state = (result, next) → resultNoInstall result ∧ evalStateNoInstall next := by
            intro location function args state next result clockLe functionOk argsOk stateOk run
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).1 location function args state next result rfl functionOk argsOk stateOk run
            · exact appAll location function args state next result clockEq functionOk argsOk stateOk run
          intro expressions env state next result stateClock measure safe envOk stateOk run
          cases expressions with
          | nil =>
            simp [ClosSem.evaluate] at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨by simp [resultNoInstall, valuesNoInstall], stateOk⟩
          | cons first rest =>
            cases rest with
            | cons second tail =>
              simp only [ClosLang.hasInstallList, Bool.or_eq_false_iff] at safe
              apply evaluate_cons_noInstall_step first (second :: tail) env state next result ?_ ?_ run
              · intro final headResult headRun
                apply exprIH [first] env state final headResult (by omega) ?_ ?_ envOk stateOk headRun
                · simp only [ClosSem.expsWeight] at measure ⊢; omega
                · simp [ClosLang.hasInstallList, safe.1]
              · intro start final tailResult bound startOk tailRun
                apply exprIH (second :: tail) env start final tailResult (by omega) ?_ (by simpa [ClosLang.hasInstallList, Bool.or_eq_false_iff] using safe.2) envOk startOk tailRun
                simp only [ClosSem.expsWeight] at measure ⊢; omega
            | nil =>
              simp only [ClosLang.hasInstallList, Bool.or_false] at safe
              cases first with
              | var trace index => exact evaluate_var_noInstall trace index env state next result envOk stateOk run
              | fn name location selected arity body =>
                exact evaluate_fn_noInstall name location selected arity body env state next result (by simpa [ClosLang.hasInstall] using safe) envOk stateOk run
              | raise trace body =>
                apply evaluate_raise_noInstall_step trace body env state next result ?_ run
                intro final bodyResult bodyRun
                apply exprIH [body] env state final bodyResult (by omega) ?_ ?_ envOk stateOk bodyRun
                · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                · simpa [ClosLang.hasInstallList, ClosLang.hasInstall] using safe
              | tick trace body =>
                apply evaluate_tick_noInstall_step trace body env state next result stateOk ?_ run
                intro start final bodyResult bound startOk bodyRun
                apply smaller [body] env start final bodyResult (by omega) ?_ envOk startOk bodyRun
                simpa [ClosLang.hasInstallList, ClosLang.hasInstall] using safe
              | call trace ticks location args =>
                apply evaluate_call_noInstall_step trace ticks location args env state next result ?_ ?_ run
                · intro final argResult argRun
                  apply exprIH args env state final argResult (by omega) ?_ ?_ envOk stateOk argRun
                  · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                  · simpa [ClosLang.hasInstall] using safe
                · intro body bodyEnv start final bodyResult bound bodyOk bodyEnvOk startOk bodyRun
                  apply smaller [body] bodyEnv start final bodyResult (by omega) ?_ bodyEnvOk startOk bodyRun
                  simp [ClosLang.hasInstallList, bodyOk]
              | «let» trace bindings body =>
                simp only [ClosLang.hasInstall, Bool.or_eq_false_iff] at safe
                apply evaluate_let_noInstall_step trace bindings body env state next result envOk ?_ ?_ run
                · intro final bindingResult bindingRun
                  apply exprIH bindings env state final bindingResult (by omega) ?_ safe.2 envOk stateOk bindingRun
                  simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                · intro bodyEnv start final bodyResult bound bodyEnvOk startOk bodyRun
                  apply exprIH [body] bodyEnv start final bodyResult (by omega) ?_ ?_ bodyEnvOk startOk bodyRun
                  · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                  · simp [ClosLang.hasInstallList, safe.1]
              | letrec names location selected functions body =>
                simp only [ClosLang.hasInstall, Bool.or_eq_false_iff] at safe
                apply evaluate_letrec_noInstall_step names location selected functions body env state next result safe.1 envOk stateOk ?_ run
                intro bodyEnv bodyEnvOk bodyRun
                apply exprIH [body] bodyEnv state next result (by omega) ?_ ?_ bodyEnvOk stateOk bodyRun
                · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                · simp [ClosLang.hasInstallList, safe.2]
              | handle trace body handler =>
                simp only [ClosLang.hasInstall, Bool.or_eq_false_iff] at safe
                apply evaluate_handle_noInstall_step trace body handler env state next result envOk ?_ ?_ run
                · intro final bodyResult bodyRun
                  apply exprIH [body] env state final bodyResult (by omega) ?_ ?_ envOk stateOk bodyRun
                  · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                  · simp [ClosLang.hasInstallList, safe.1]
                · intro value start final handlerResult bound valueOk handlerEnvOk startOk handlerRun
                  apply exprIH [handler] (value :: env) start final handlerResult (by omega) ?_ ?_ handlerEnvOk startOk handlerRun
                  · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                  · simp [ClosLang.hasInstallList, safe.2]
              | ifThenElse trace condition yes no =>
                simp only [ClosLang.hasInstall, Bool.or_eq_false_iff] at safe
                apply evaluate_if_noInstall_step trace condition yes no env state next result ?_ ?_ run
                · intro final testResult testRun
                  apply exprIH [condition] env state final testResult (by omega) ?_ ?_ envOk stateOk testRun
                  · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                  · simp [ClosLang.hasInstallList, safe.1.1]
                · intro choice start final branchResult bound startOk branchRun
                  cases choice with
                  | false =>
                    apply exprIH [no] env start final branchResult (by omega) ?_ ?_ envOk startOk branchRun
                    · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                    · simp [ClosLang.hasInstallList, safe.2]
                  | true =>
                    apply exprIH [yes] env start final branchResult (by omega) ?_ ?_ envOk startOk branchRun
                    · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                    · simp [ClosLang.hasInstallList, safe.1.2]
              | app trace location function args =>
                simp only [ClosLang.hasInstall, Bool.or_eq_false_iff] at safe
                apply evaluate_app_noInstall_step trace location function args env state next result stateOk ?_ ?_ ?_ run
                · intro final argResult argRun
                  apply exprIH args env state final argResult (by omega) ?_ safe.2 envOk stateOk argRun
                  simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                · intro start final functionResult bound startOk functionRun
                  apply exprIH [function] env start final functionResult (by omega) ?_ ?_ envOk startOk functionRun
                  · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                  · simp [ClosLang.hasInstallList, safe.1]
                · intro value arguments start final appResult bound valueOk argumentsOk startOk appRun
                  exact appBound location value arguments start final appResult (by omega) valueOk argumentsOk startOk appRun
              | op trace op args =>
                have argsSmaller : ClosSem.expsWeight args < weight := by
                  have h := ClosSem.opWeight_gt trace op args
                  simp only [ClosSem.expsWeight] at measure
                  omega
                have argsSafe : ClosLang.hasInstallList args = false := by
                  cases op <;> simp_all [ClosLang.hasInstall]
                have argsIH : ∀ (last : ClosSem.State C F) (argResult : Result (List ClosSem.Value) ClosSem.Value),
                    ClosSem.evaluate args env state = (argResult, last) → resultNoInstall argResult ∧ evalStateNoInstall last := by
                  intro last argResult argRun
                  exact exprIH args env state last argResult (by omega) argsSmaller argsSafe envOk stateOk argRun
                have ordinary : ∀ op, op ≠ .install → op ≠ .thunkOp .forceThunk →
                    ClosSem.evaluate [.op trace op args] env state = (result, next) → resultNoInstall result ∧ evalStateNoInstall next := by
                  intro op notInstall notForce opRun
                  exact evaluate_ordinaryOp_noInstall_step trace op args env state next result notInstall notForce argsIH opRun
                cases op with
                | install => simp [ClosLang.hasInstall] at safe
                | thunkOp operation =>
                  cases operation with
                  | forceThunk =>
                    apply evaluate_force_noInstall_step trace args env state next result argsIH ?_ run
                    intro value start final forceResult bound valueOk startOk forceRun
                    apply exprIH [ClosSem.appUnit (.var .none 0)] [value] start final forceResult (by omega) ?_ ?_ ?_ startOk forceRun
                    · have h := ClosSem.appUnit_var_weight
                      simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure
                      simp only [ClosSem.appUnit, ClosSem.expsWeight, ClosSem.expWeight] at h ⊢
                      omega
                    · simp [ClosSem.appUnit, ClosLang.hasInstallList, ClosLang.hasInstall]
                    · simp [valuesNoInstall, valueOk]
                  | allocThunk mode => exact ordinary (.thunkOp (.allocThunk mode)) (by simp) (by simp) run
                  | updateThunk mode => exact ordinary (.thunkOp (.updateThunk mode)) (by simp) (by simp) run
                | label index => exact ordinary (.label index) (by simp) (by simp) run
                | ffi name => exact ordinary (.ffi name) (by simp) (by simp) run
                | intOp operation => exact ordinary (.intOp operation) (by simp) (by simp) run
                | wordOp operation => exact ordinary (.wordOp operation) (by simp) (by simp) run
                | blockOp operation => exact ordinary (.blockOp operation) (by simp) (by simp) run
                | globOp operation => exact ordinary (.globOp operation) (by simp) (by simp) run
                | memOp operation => exact ordinary (.memOp operation) (by simp) (by simp) run
  constructor
  · intro expressions env state next result safe envOk stateOk run
    exact (all state.clock).2 (ClosSem.expsWeight expressions) expressions env state next result rfl rfl safe envOk stateOk run
  · intro location function args state next result functionOk argsOk stateOk run
    exact (all state.clock).1 location function args state next result rfl functionOk argsOk stateOk run

end Flapjack.Compiler.Backend.ClosInterp
