import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallAppRelation

/-! Mutual equal-clock no-install simulation for the proof-side evaluator.
The evaluator and state carriers await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Related executions of no-install expressions and closures agree and
preserve the no-install relation. -/
theorem evaluate_noInstall_simulation {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
      (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosLang.hasInstallList expressions = false → valuesNoInstall env = true → StateRelNoInstall source target →
      ClosSem.evaluate expressions env source = (result, sourceFinal) →
      ∃ targetFinal, ClosSem.evaluate expressions env target = (result, targetFinal) ∧
        StateRelNoInstall sourceFinal targetFinal ∧ resultNoInstall result) ∧
    (∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
      (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      valueNoInstall function = true → valuesNoInstall args = true → StateRelNoInstall source target →
      ClosSem.evaluateApp location function args source = (result, sourceFinal) →
      ∃ targetFinal, ClosSem.evaluateApp location function args target = (result, targetFinal) ∧
        StateRelNoInstall sourceFinal targetFinal ∧ resultNoInstall result) := by
  have all : ∀ clock : Nat,
      (∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
        (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
        source.clock = clock → valueNoInstall function = true → valuesNoInstall args = true → StateRelNoInstall source target →
        ClosSem.evaluateApp location function args source = (result, sourceFinal) →
        ∃ targetFinal, ClosSem.evaluateApp location function args target = (result, targetFinal) ∧
          StateRelNoInstall sourceFinal targetFinal ∧ resultNoInstall result) ∧
      (∀ (weight : Nat) (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
        (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
        source.clock = clock → ClosSem.expsWeight expressions = weight → ClosLang.hasInstallList expressions = false →
        valuesNoInstall env = true → StateRelNoInstall source target →
        ClosSem.evaluate expressions env source = (result, sourceFinal) →
        ∃ targetFinal, ClosSem.evaluate expressions env target = (result, targetFinal) ∧
          StateRelNoInstall sourceFinal targetFinal ∧ resultNoInstall result) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
          (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
          source.clock = clock → valueNoInstall function = true → valuesNoInstall args = true → StateRelNoInstall source target →
          ClosSem.evaluateApp location function args source = (result, sourceFinal) →
          ∃ targetFinal, ClosSem.evaluateApp location function args target = (result, targetFinal) ∧
            StateRelNoInstall sourceFinal targetFinal ∧ resultNoInstall result := by
        intro location function args source target sourceFinal result stateClock functionOk argsOk related run
        apply evaluateApp_noInstall_relation_step location function args source target sourceFinal result functionOk argsOk ?_ ?_ related run
        · intro body env start target final bodyResult smaller bodyOk envOk bodyRun bodyRel
          exact (clockIH start.clock (by omega)).2 (ClosSem.expsWeight [body]) [body] env start target final bodyResult rfl rfl
            (by simp [ClosLang.hasInstallList, bodyOk]) envOk bodyRel bodyRun
        · intro value remaining start target final appResult smaller valueOk remainingOk appRun appRel
          exact (clockIH start.clock (by omega)).1 location value remaining start target final appResult rfl valueOk remainingOk appRel appRun
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
              (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
              source.clock ≤ clock → ClosSem.expsWeight expressions < weight → ClosLang.hasInstallList expressions = false →
              valuesNoInstall env = true → StateRelNoInstall source target →
              ClosSem.evaluate expressions env source = (result, sourceFinal) →
              ∃ targetFinal, ClosSem.evaluate expressions env target = (result, targetFinal) ∧
                StateRelNoInstall sourceFinal targetFinal ∧ resultNoInstall result := by
            intro expressions env source target final result clockLe weightLt safe envOk related run
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH source.clock clockLt).2 (ClosSem.expsWeight expressions) expressions env source target final result rfl rfl safe envOk related run
            · exact weightIH (ClosSem.expsWeight expressions) weightLt expressions env source target final result clockEq rfl safe envOk related run
          have smaller : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
              (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
              source.clock < clock → ClosLang.hasInstallList expressions = false → valuesNoInstall env = true → StateRelNoInstall source target →
              ClosSem.evaluate expressions env source = (result, sourceFinal) →
              ∃ targetFinal, ClosSem.evaluate expressions env target = (result, targetFinal) ∧
                StateRelNoInstall sourceFinal targetFinal ∧ resultNoInstall result := by
            intro expressions env source target final result clockLt safe envOk related run
            exact (clockIH source.clock clockLt).2 (ClosSem.expsWeight expressions) expressions env source target final result rfl rfl safe envOk related run
          have appBound : ∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
              (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
              source.clock ≤ clock → valueNoInstall function = true → valuesNoInstall args = true → StateRelNoInstall source target →
              ClosSem.evaluateApp location function args source = (result, sourceFinal) →
              ∃ targetFinal, ClosSem.evaluateApp location function args target = (result, targetFinal) ∧
                StateRelNoInstall sourceFinal targetFinal ∧ resultNoInstall result := by
            intro location function args source target final result clockLe functionOk argsOk related run
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH source.clock clockLt).1 location function args source target final result rfl functionOk argsOk related run
            · exact appAll location function args source target final result clockEq functionOk argsOk related run
          intro expressions env source target final result stateClock measure safe envOk related run
          cases expressions with
          | nil =>
            simp [ClosSem.evaluate] at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨target, by simp [ClosSem.evaluate], related, by simp [resultNoInstall, valuesNoInstall]⟩
          | cons first rest =>
            cases rest with
            | cons second tail =>
              simp only [ClosLang.hasInstallList, Bool.or_eq_false_iff] at safe
              apply evaluate_cons_noInstall_relation_step first (second :: tail) env source target final result ?_ ?_ related run
              · intro target last headResult headRun headRel
                apply exprIH [first] env source target last headResult (by omega) ?_ ?_ envOk headRel headRun
                · simp only [ClosSem.expsWeight] at measure ⊢; omega
                · simp [ClosLang.hasInstallList, safe.1]
              · intro start target last tailResult bound tailRun tailRel
                apply exprIH (second :: tail) env start target last tailResult (by omega) ?_ (by simpa [ClosLang.hasInstallList, Bool.or_eq_false_iff] using safe.2) envOk tailRel tailRun
                simp only [ClosSem.expsWeight] at measure ⊢; omega
            | nil =>
              simp only [ClosLang.hasInstallList, Bool.or_false] at safe
              cases first with
              | var trace index => exact evaluate_var_noInstall_relation trace index env source target final result envOk related run
              | fn name location selected arity body =>
                exact evaluate_fn_noInstall_relation name location selected arity body env source target final result (by simpa [ClosLang.hasInstall] using safe) envOk related run
              | raise trace body =>
                apply evaluate_raise_noInstall_relation_step trace body env source target final result ?_ related run
                intro target last bodyResult bodyRun bodyRel
                apply exprIH [body] env source target last bodyResult (by omega) ?_ ?_ envOk bodyRel bodyRun
                · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                · simpa [ClosLang.hasInstallList, ClosLang.hasInstall] using safe
              | tick trace body =>
                apply evaluate_tick_noInstall_relation_step trace body env source target final result ?_ related run
                intro start target last bodyResult bound bodyRun bodyRel
                apply smaller [body] env start target last bodyResult (by omega) ?_ envOk bodyRel bodyRun
                simpa [ClosLang.hasInstallList, ClosLang.hasInstall] using safe
              | call trace ticks location args =>
                apply evaluate_call_noInstall_relation_step trace ticks location args env source target final result ?_ related run
                intro target last argResult argRun argRel
                apply exprIH args env source target last argResult (by omega) ?_ ?_ envOk argRel argRun
                · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                · simpa [ClosLang.hasInstall] using safe
              | «let» trace bindings body =>
                simp only [ClosLang.hasInstall, Bool.or_eq_false_iff] at safe
                apply evaluate_let_noInstall_relation_step trace bindings body env source target final result envOk ?_ ?_ related run
                · intro target last bindingResult bindingRun bindingRel
                  apply exprIH bindings env source target last bindingResult (by omega) ?_ safe.2 envOk bindingRel bindingRun
                  simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                · intro bodyEnv start target last bodyResult bound bodyEnvOk bodyRun bodyRel
                  apply exprIH [body] bodyEnv start target last bodyResult (by omega) ?_ ?_ bodyEnvOk bodyRel bodyRun
                  · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                  · simp [ClosLang.hasInstallList, safe.1]
              | letrec names location selected functions body =>
                simp only [ClosLang.hasInstall, Bool.or_eq_false_iff] at safe
                apply evaluate_letrec_noInstall_relation_step names location selected functions body env source target final result safe.1 envOk ?_ related run
                intro bodyEnv target last bodyResult bodyEnvOk bodyRun bodyRel
                apply exprIH [body] bodyEnv source target last bodyResult (by omega) ?_ ?_ bodyEnvOk bodyRel bodyRun
                · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                · simp [ClosLang.hasInstallList, safe.2]
              | handle trace body handler =>
                simp only [ClosLang.hasInstall, Bool.or_eq_false_iff] at safe
                apply evaluate_handle_noInstall_relation_step trace body handler env source target final result envOk ?_ ?_ related run
                · intro target last bodyResult bodyRun bodyRel
                  apply exprIH [body] env source target last bodyResult (by omega) ?_ ?_ envOk bodyRel bodyRun
                  · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                  · simp [ClosLang.hasInstallList, safe.1]
                · intro value start target last handlerResult bound handlerEnvOk handlerRun handlerRel
                  apply exprIH [handler] (value :: env) start target last handlerResult (by omega) ?_ ?_ handlerEnvOk handlerRel handlerRun
                  · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                  · simp [ClosLang.hasInstallList, safe.2]
              | ifThenElse trace condition yes no =>
                simp only [ClosLang.hasInstall, Bool.or_eq_false_iff] at safe
                apply evaluate_if_noInstall_relation_step trace condition yes no env source target final result ?_ ?_ related run
                · intro target last testResult testRun testRel
                  apply exprIH [condition] env source target last testResult (by omega) ?_ ?_ envOk testRel testRun
                  · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                  · simp [ClosLang.hasInstallList, safe.1.1]
                · intro choice start target last branchResult bound branchRun branchRel
                  cases choice with
                  | false =>
                    apply exprIH [no] env start target last branchResult (by omega) ?_ ?_ envOk branchRel branchRun
                    · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                    · simp [ClosLang.hasInstallList, safe.2]
                  | true =>
                    apply exprIH [yes] env start target last branchResult (by omega) ?_ ?_ envOk branchRel branchRun
                    · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                    · simp [ClosLang.hasInstallList, safe.1.2]
              | app trace location function args =>
                simp only [ClosLang.hasInstall, Bool.or_eq_false_iff] at safe
                apply evaluate_app_noInstall_relation_step trace location function args env source target final result ?_ ?_ ?_ related run
                · intro target last argResult argRun argRel
                  apply exprIH args env source target last argResult (by omega) ?_ safe.2 envOk argRel argRun
                  simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                · intro start target last functionResult bound functionRun functionRel
                  apply exprIH [function] env start target last functionResult (by omega) ?_ ?_ envOk functionRel functionRun
                  · simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                  · simp [ClosLang.hasInstallList, safe.1]
                · intro value arguments start target last appResult bound valueOk argumentsOk appRun appRel
                  exact appBound location value arguments start target last appResult (by omega) valueOk argumentsOk appRel appRun
              | op trace op args =>
                have argsSmaller : ClosSem.expsWeight args < weight := by
                  have h := ClosSem.opWeight_gt trace op args
                  simp only [ClosSem.expsWeight] at measure
                  omega
                have argsSafe : ClosLang.hasInstallList args = false := by
                  cases op <;> simp_all [ClosLang.hasInstall]
                have argsIH : ∀ (target last : ClosSem.State C F) (argResult : Result (List ClosSem.Value) ClosSem.Value),
                    ClosSem.evaluate args env source = (argResult, last) → StateRelNoInstall source target →
                    ∃ targetLast, ClosSem.evaluate args env target = (argResult, targetLast) ∧
                      StateRelNoInstall last targetLast ∧ resultNoInstall argResult := by
                  intro target last argResult argRun argRel
                  exact exprIH args env source target last argResult (by omega) argsSmaller argsSafe envOk argRel argRun
                have ordinary : ∀ op, op ≠ .install → op ≠ .thunkOp .forceThunk →
                    ClosSem.evaluate [.op trace op args] env source = (result, final) →
                    ∃ targetFinal, ClosSem.evaluate [.op trace op args] env target = (result, targetFinal) ∧
                      StateRelNoInstall final targetFinal ∧ resultNoInstall result := by
                  intro op notInstall notForce opRun
                  exact evaluate_ordinaryOp_noInstall_relation_step trace op args env source target final result notInstall notForce argsIH related opRun
                cases op with
                | install => simp [ClosLang.hasInstall] at safe
                | thunkOp operation =>
                  cases operation with
                  | forceThunk =>
                    apply evaluate_force_noInstall_relation_step trace args env source target final result argsIH ?_ related run
                    intro value start target last forceResult bound valueOk forceRun forceRel
                    apply exprIH [ClosSem.appUnit (.var .none 0)] [value] start target last forceResult (by omega) ?_ ?_ ?_ forceRel forceRun
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
  · intro expressions env source target final result safe envOk related run
    exact (all source.clock).2 (ClosSem.expsWeight expressions) expressions env source target final result rfl rfl safe envOk related run
  · intro location function args source target final result functionOk argsOk related run
    exact (all source.clock).1 location function args source target final result rfl functionOk argsOk related run

/-- For an attached program without installation, the two initial compiler
configurations agree at the same clock and preserve the no-install relation. -/
theorem attachInterpreter_noInstall_initial_simulation {C F : Type} (expressions : List ClosLang.Exp)
    (ffi : HolFfiState F) (maxApp clock : Nat) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C) (sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (safe : ClosLang.hasInstallList expressions = false)
    (oracleSafe : ∀ index, (oracle index).2.2 = []) (positive : 1 ≤ maxApp)
    (run : ClosSem.evaluate (attachInterpreter expressions) []
      (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle
        (Flapjack.Compiler.Backend.BackendProps.pureCc insertProgram compiler) clock) = (result, sourceFinal)) :
    ∃ targetFinal, ClosSem.evaluate (attachInterpreter expressions) []
      (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty
        (Flapjack.Compiler.Backend.BackendProps.pureCo insertProgram ∘ oracle) compiler clock) = (result, targetFinal) ∧
      StateRelNoInstall sourceFinal targetFinal ∧ resultNoInstall result := by
  exact evaluate_noInstall_simulation.1 (attachInterpreter expressions) [] _ _ sourceFinal result
    (attachInterpreter_noInstall expressions safe) (by simp [valuesNoInstall])
    (initialStates_noInstall ffi maxApp clock oracle compiler oracleSafe positive) run

end Flapjack.Compiler.Backend.ClosInterp
