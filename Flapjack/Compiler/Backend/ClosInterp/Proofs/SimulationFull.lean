import Flapjack.Compiler.Backend.ClosInterp.Proofs.ControlRelation

/-! Clocked evaluator simulation for interpreter insertion. The evaluator and
state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Related proof-side evaluator states simulate evaluation and application. -/
theorem evaluate_simulation {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
      (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate expressions env source = (result, sourceFinal) → StateRel source target →
      result ≠ .err (.abort .typeError) → ∃ extra targetFinal,
        ClosSem.evaluate expressions env { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal) ∧
    (∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
      (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluateApp location function args source = (result, sourceFinal) → StateRel source target →
      result ≠ .err (.abort .typeError) → ∃ extra targetFinal,
        ClosSem.evaluateApp location function args { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal) := by
  have all : ∀ clock : Nat,
      (∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
        (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
        source.clock = clock → ClosSem.evaluateApp location function args source = (result, sourceFinal) → StateRel source target →
        result ≠ .err (.abort .typeError) → ∃ extra targetFinal,
          ClosSem.evaluateApp location function args { target with clock := extra + target.clock } = (result, targetFinal) ∧
          StateRel sourceFinal targetFinal) ∧
      (∀ (weight : Nat) (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
        (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
        source.clock = clock → ClosSem.expsWeight expressions = weight →
        ClosSem.evaluate expressions env source = (result, sourceFinal) → StateRel source target →
        result ≠ .err (.abort .typeError) → ∃ extra targetFinal,
          ClosSem.evaluate expressions env { target with clock := extra + target.clock } = (result, targetFinal) ∧
          StateRel sourceFinal targetFinal) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
          (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
          source.clock = clock → ClosSem.evaluateApp location function args source = (result, sourceFinal) → StateRel source target →
          result ≠ .err (.abort .typeError) → ∃ extra targetFinal,
            ClosSem.evaluateApp location function args { target with clock := extra + target.clock } = (result, targetFinal) ∧
            StateRel sourceFinal targetFinal := by
        intro location function args source target sourceFinal result stateClock run related notTypeError
        apply evaluateApp_simulation_step location function args source target sourceFinal result ?_ ?_ related run notTypeError
        · intro body env bodySource bodyTarget bodyFinal bodyResult smaller bodyRun bodyRel bodyNotTypeError
          exact (clockIH bodySource.clock (by omega)).2 (ClosSem.expsWeight [body]) [body] env bodySource bodyTarget bodyFinal
            bodyResult rfl rfl bodyRun bodyRel bodyNotTypeError
        · intro value rest appSource appTarget appFinal appResult smaller appRun appRel appNotTypeError
          exact (clockIH appSource.clock (by omega)).1 location value rest appSource appTarget appFinal appResult rfl appRun appRel appNotTypeError
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
              (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
              source.clock ≤ clock → ClosSem.expsWeight expressions < weight →
              ClosSem.evaluate expressions env source = (result, sourceFinal) → StateRel source target →
              result ≠ .err (.abort .typeError) → ∃ extra targetFinal,
                ClosSem.evaluate expressions env { target with clock := extra + target.clock } = (result, targetFinal) ∧
                StateRel sourceFinal targetFinal := by
            intro expressions env source target sourceFinal result clockLe weightLt run related notTypeError
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH source.clock clockLt).2 (ClosSem.expsWeight expressions) expressions env source target sourceFinal result rfl rfl run related notTypeError
            · exact weightIH (ClosSem.expsWeight expressions) weightLt expressions env source target sourceFinal result clockEq rfl run related notTypeError
          have smaller : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
              (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
              source.clock < clock → ClosSem.evaluate expressions env source = (result, sourceFinal) → StateRel source target →
              result ≠ .err (.abort .typeError) → ∃ extra targetFinal,
                ClosSem.evaluate expressions env { target with clock := extra + target.clock } = (result, targetFinal) ∧
                StateRel sourceFinal targetFinal := by
            intro expressions env source target sourceFinal result clockLt run related notTypeError
            exact (clockIH source.clock clockLt).2 (ClosSem.expsWeight expressions) expressions env source target sourceFinal result rfl rfl run related notTypeError
          have appBound : ∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
              (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
              source.clock ≤ clock → ClosSem.evaluateApp location function args source = (result, sourceFinal) → StateRel source target →
              result ≠ .err (.abort .typeError) → ∃ extra targetFinal,
                ClosSem.evaluateApp location function args { target with clock := extra + target.clock } = (result, targetFinal) ∧
                StateRel sourceFinal targetFinal := by
            intro location function args source target sourceFinal result clockLe run related notTypeError
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH source.clock clockLt).1 location function args source target sourceFinal result rfl run related notTypeError
            · exact appAll location function args source target sourceFinal result clockEq run related notTypeError
          intro expressions env source target sourceFinal result stateClock measure run related notTypeError
          cases expressions with
          | nil =>
            simp [ClosSem.evaluate] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨0, target, ?_, related⟩
            simp [ClosSem.evaluate]
          | cons first rest =>
            cases rest with
            | cons second tail =>
              apply evaluate_cons_simulation_step first (second :: tail) env source target sourceFinal result ?_ ?_ related run notTypeError
              · intro target final result run related notTypeError
                apply exprIH [first] env source target final result (by omega) ?_ run related notTypeError
                simp only [ClosSem.expsWeight] at measure ⊢
                omega
              · intro tailSource tailTarget tailFinal tailResult bound tailRun tailRelated tailNotTypeError
                apply exprIH (second :: tail) env tailSource tailTarget tailFinal tailResult (by omega) ?_ tailRun tailRelated tailNotTypeError
                simp only [ClosSem.expsWeight] at measure ⊢
                omega
            | nil =>
              cases first with
              | var trace index => exact evaluate_var_simulation trace index env source target sourceFinal result related run notTypeError
              | fn name location selected arity body =>
                exact evaluate_fn_simulation name location selected arity body env source target sourceFinal result related run notTypeError
              | raise trace body =>
                apply evaluate_raise_simulation_step trace body env source target sourceFinal result ?_ related run notTypeError
                intro target final result run related notTypeError
                apply exprIH [body] env source target final result (by omega) ?_ run related notTypeError
                simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
              | tick trace body =>
                apply evaluate_tick_simulation_step trace body env source target sourceFinal result ?_ related run notTypeError
                intro bodySource bodyTarget bodyFinal bodyResult bound bodyRun bodyRel bodyNotTypeError
                exact smaller [body] env bodySource bodyTarget bodyFinal bodyResult (by omega) bodyRun bodyRel bodyNotTypeError
              | call trace ticks location args =>
                apply evaluate_call_simulation_step trace ticks location args env source target sourceFinal result ?_ related run notTypeError
                intro target final result run related notTypeError
                apply exprIH args env source target final result (by omega) ?_ run related notTypeError
                simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
              | «let» trace bindings body =>
                apply evaluate_let_simulation_step trace bindings body env source target sourceFinal result ?_ ?_ related run notTypeError
                · intro target final result run related notTypeError
                  apply exprIH bindings env source target final result (by omega) ?_ run related notTypeError
                  simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                · intro values bodySource bodyTarget bodyFinal bodyResult bound bodyRun bodyRel bodyNotTypeError
                  apply exprIH [body] (values ++ env) bodySource bodyTarget bodyFinal bodyResult (by omega) ?_ bodyRun bodyRel bodyNotTypeError
                  simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
              | letrec names location selected functions body =>
                apply evaluate_letrec_simulation_step names location selected functions body env source target sourceFinal result ?_ related run notTypeError
                intro newEnv target final result run related notTypeError
                apply exprIH [body] newEnv source target final result (by omega) ?_ run related notTypeError
                simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
              | handle trace body handler =>
                apply evaluate_handle_simulation_step trace body handler env source target sourceFinal result ?_ ?_ related run notTypeError
                · intro target final result run related notTypeError
                  apply exprIH [body] env source target final result (by omega) ?_ run related notTypeError
                  simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                · intro value bodySource bodyTarget bodyFinal bodyResult bound bodyRun bodyRel bodyNotTypeError
                  apply exprIH [handler] (value :: env) bodySource bodyTarget bodyFinal bodyResult (by omega) ?_ bodyRun bodyRel bodyNotTypeError
                  simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
              | ifThenElse trace condition yes no =>
                apply evaluate_if_simulation_step trace condition yes no env source target sourceFinal result ?_ ?_ related run notTypeError
                · intro target final result run related notTypeError
                  apply exprIH [condition] env source target final result (by omega) ?_ run related notTypeError
                  simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                · intro choice conditionSource conditionTarget conditionFinal branchResult bound branchRun branchRel branchNotTypeError
                  cases choice with
                  | false =>
                    apply exprIH [no] env conditionSource conditionTarget conditionFinal branchResult (by omega) ?_ branchRun branchRel branchNotTypeError
                    simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                  | true =>
                    apply exprIH [yes] env conditionSource conditionTarget conditionFinal branchResult (by omega) ?_ branchRun branchRel branchNotTypeError
                    simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
              | app trace location function args =>
                apply evaluate_app_simulation_step trace location function args env source target sourceFinal result ?_ ?_ ?_ related run notTypeError
                · intro target final result run related notTypeError
                  apply exprIH args env source target final result (by omega) ?_ run related notTypeError
                  simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                · intro fnSource fnTarget fnFinal fnResult bound fnRun fnRel fnNotTypeError
                  apply exprIH [function] env fnSource fnTarget fnFinal fnResult (by omega) ?_ fnRun fnRel fnNotTypeError
                  simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢; omega
                · intro fn values appSource appTarget appFinal appResult bound appRun appRel appNotTypeError
                  exact appBound location fn values appSource appTarget appFinal appResult (by omega) appRun appRel appNotTypeError
              | op trace op args =>
                have argsSmaller : ClosSem.expsWeight args < weight := by
                  have h := ClosSem.opWeight_gt trace op args
                  simp only [ClosSem.expsWeight] at measure
                  omega
                have argsSim : ∀ (target final : ClosSem.State C F) (argResult : Result (List ClosSem.Value) ClosSem.Value),
                    ClosSem.evaluate args env source = (argResult, final) → StateRel source target → argResult ≠ .err (.abort .typeError) →
                    ∃ extra targetFinal, ClosSem.evaluate args env { target with clock := extra + target.clock } = (argResult, targetFinal) ∧
                      StateRel final targetFinal := by
                  intro target final argResult argRun argRel argNotTypeError
                  exact exprIH args env source target final argResult (by omega) argsSmaller argRun argRel argNotTypeError
                have ordinary : ∀ op, op ≠ .install → op ≠ .thunkOp .forceThunk →
                    ClosSem.evaluate [.op trace op args] env source = (result, sourceFinal) →
                    ∃ extra targetFinal, ClosSem.evaluate [.op trace op args] env { target with clock := extra + target.clock } =
                      (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
                  intro op notInstall notForce opRun
                  exact evaluate_ordinaryOp_simulation_step trace op args env source target sourceFinal result notInstall notForce
                    argsSim related opRun notTypeError
                cases op with
                | install =>
                  apply evaluate_install_simulation_step trace args env source target sourceFinal result argsSim ?_ related run notTypeError
                  intro program installedSource installedTarget installedFinal installedResult bound installedRun installedRel installedNotTypeError
                  have installedAssumption : InterpAssum C F installedSource.clock := by
                    constructor
                    · intro xs st e target res final clockLe eval notTypeError rel
                      exact smaller xs e st target final res (by omega) eval rel notTypeError
                    · intro vs st loc fn target res final clockLe app notTypeError rel
                      exact (clockIH st.clock (by omega)).1 loc fn vs st target final res rfl app rel notTypeError
                  exact insertInterp_correct program installedSource installedTarget installedFinal installedResult installedRun installedAssumption installedRel installedNotTypeError
                | thunkOp operation =>
                  cases operation with
                  | forceThunk =>
                    apply evaluate_force_simulation_step trace args env source target sourceFinal result argsSim ?_ related run notTypeError
                    intro value forceSource forceTarget forceFinal forceResult bound forceRun forceRel forceNotTypeError
                    apply exprIH [ClosSem.appUnit (.var .none 0)] [value] forceSource forceTarget forceFinal forceResult (by omega) ?_ forceRun forceRel forceNotTypeError
                    have h := ClosSem.appUnit_var_weight
                    simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure
                    simp only [ClosSem.appUnit, ClosSem.expsWeight, ClosSem.expWeight] at h ⊢
                    omega
                  | allocThunk mode => exact ordinary _ (by simp) (by simp) run
                  | updateThunk mode => exact ordinary _ (by simp) (by simp) run
                | label _ | ffi _ | intOp _ | wordOp _ | blockOp _ | globOp _ | memOp _ =>
                  exact ordinary _ (by simp) (by simp) run
  constructor
  · intro expressions env source target sourceFinal result run related notTypeError
    exact (all source.clock).2 (ClosSem.expsWeight expressions) expressions env source target sourceFinal result rfl rfl run related notTypeError
  · intro location function args source target sourceFinal result run related notTypeError
    exact (all source.clock).1 location function args source target sourceFinal result rfl run related notTypeError

/-- The clock-bounded simulation assumption holds for every bound. -/
theorem interpAssum_all {C F : Type} (bound : Nat) : InterpAssum C F bound := by
  constructor
  · intro expressions source env target result sourceFinal _ run notTypeError related
    exact evaluate_simulation.1 expressions env source target sourceFinal result run related notTypeError
  · intro args source location function target result sourceFinal _ run notTypeError related
    exact evaluate_simulation.2 location function args source target sourceFinal result run related notTypeError

/-- Interpreter insertion simulates evaluation without an extra simulation
assumption. This remains proof-side until the evaluator and state carriers
have been reviewed against their HOL counterparts. -/
theorem insertInterp_simulates {C F : Type} (expressions : List ClosLang.Exp)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate expressions [] source = (result, sourceFinal))
    (related : StateRel source target) (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate (insertInterp expressions) [] { target with clock := extra + target.clock } =
        (result, targetFinal) ∧ StateRel sourceFinal targetFinal :=
  insertInterp_correct expressions source target sourceFinal result run (interpAssum_all source.clock) related notTypeError

end Flapjack.Compiler.Backend.ClosInterp
