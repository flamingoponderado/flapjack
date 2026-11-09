module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.LocalSteps

@[expose] public section

/-! Mutual evaluator simulation for closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem

/-- The proof-side annotation evaluator and closure application simulate one
another. The evaluator, its primitive dispatcher, and carriers remain subject
to HOL correspondence review; this is not tagged as a HOL theorem. -/
theorem evaluate_simulation {C F : Type} :
    (∀ expressions, EvalSimulation (C := C) (F := F) expressions) ∧
      (∀ clock, AppSimulationClockBelow (C := C) (F := F) clock) := by
  have all : ∀ clock : Nat,
      (∀ source : State C F, source.clock = clock →
        ∀ requested function nextFunction args nextArgs target result sourceNext,
          evaluateApp requested function args source = (result, sourceNext) →
          result ≠ .err (.abort .typeError) → ValueRel function nextFunction →
          List.Forall₂ ValueRel args nextArgs → CodeSafe source → OracleSafe source → StateRel source target →
          ∃ targetResult targetNext, evaluateApp requested nextFunction nextArgs target = (targetResult, targetNext) ∧
            ResultRel result targetResult ∧ StateRel sourceNext targetNext) ∧
      (∀ weight expressions (source : State C F),
        source.clock = clock → expsWeight expressions = weight → EvalSimulationAt source expressions) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ source : State C F, source.clock = clock →
          ∀ requested function nextFunction args nextArgs target result sourceNext,
            evaluateApp requested function args source = (result, sourceNext) →
            result ≠ .err (.abort .typeError) → ValueRel function nextFunction →
            List.Forall₂ ValueRel args nextArgs → CodeSafe source → OracleSafe source → StateRel source target →
            ∃ targetResult targetNext, evaluateApp requested nextFunction nextArgs target = (targetResult, targetNext) ∧
              ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
        intro source clockEq requested function nextFunction args nextArgs target result sourceNext run noType related argsRel code oracle states
        apply evaluateApp_clock_step requested function nextFunction args nextArgs source target result sourceNext
          run noType related argsRel code oracle states
        · intro body state smaller
          exact (clockIH state.clock (by omega)).2 (expsWeight [body]) [body] state rfl rfl
        · intro requested function nextFunction args nextArgs state target result next smaller appRun appNoType rel argsRel code oracle states
          exact (clockIH state.clock (by omega)).1 state rfl requested function nextFunction args nextArgs target
            result next appRun appNoType rel argsRel code oracle states
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ expressions (state : State C F), state.clock ≤ clock →
              expsWeight expressions < weight → EvalSimulationAt state expressions := by
            intro expressions state clockLe weightLt
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions state rfl rfl
            · exact weightIH (expsWeight expressions) weightLt expressions state clockEq rfl
          have appBound : AppSimulationClockBelow (C := C) (F := F) (clock + 1) := by
            intro requested function nextFunction args nextArgs state target result next smaller run noType rel argsRel code oracle states
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ smaller) with clockLt | clockEq
            · exact (clockIH state.clock clockLt).1 state rfl requested function nextFunction args nextArgs target
                result next run noType rel argsRel code oracle states
            · exact appAll state clockEq requested function nextFunction args nextArgs target result next
                run noType rel argsRel code oracle states
          intro expressions source clockEq measure
          cases expressions with
          | nil => exact evalSimulation_at evaluate_nil source
          | cons first rest =>
            cases rest with
            | cons second tail =>
              apply evaluate_cons_step first second tail source
              · apply exprIH [first] source (by omega)
                simp only [expsWeight] at measure ⊢; omega
              · intro state bound
                apply exprIH (second :: tail) state (by omega)
                simp only [expsWeight] at measure ⊢; omega
            | nil =>
              cases first with
              | var trace index => exact evalSimulation_at (evaluate_var trace index) source
              | fn name location selected arity body =>
                exact evalSimulation_at (evaluate_fn name location selected arity body) source
              | raise trace body =>
                apply evaluate_raise_step trace body source
                apply exprIH [body] source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | tick trace body =>
                apply evaluate_tick_step trace body source
                apply exprIH [body] (decClock 1 source) (by simp [decClock]; omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | call trace ticks location args =>
                apply evaluate_call_step trace ticks location args source
                · apply exprIH args source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro body state smaller
                  exact (clockIH state.clock (by omega)).2 (expsWeight [body]) [body] state rfl rfl
              | «let» trace bindings body =>
                apply evaluate_let_step trace bindings body source
                · apply exprIH bindings source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [body] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | letrec names location selected functions body =>
                apply evaluate_letrec_step names location selected functions body source
                apply exprIH [body] source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | handle trace body handler =>
                apply evaluate_handle_step trace body handler source
                · apply exprIH [body] source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [handler] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | ifThenElse trace condition yes no =>
                apply evaluate_if_step trace condition yes no source
                · apply exprIH [condition] source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [yes] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [no] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | app trace location function args =>
                apply evaluate_app_step trace location function args source
                · apply exprIH args source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [function] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · simpa [clockEq] using appBound
              | op trace op args =>
                have argsSmaller : expsWeight args < weight := by
                  have h := opWeight_gt trace op args
                  simp only [expsWeight] at measure
                  omega
                have argsIH := exprIH args source (by omega) argsSmaller
                have ordinary : ∀ op, op ≠ .install → op ≠ .thunkOp .forceThunk →
                    EvalSimulationAt source [.op trace op args] := by
                  intro op notInstall notForce
                  exact evaluate_ordinary_all_step trace op args notInstall notForce source argsIH
                cases op with
                | install =>
                  apply evaluate_install_step trace args source argsIH
                  intro program state smaller
                  exact (clockIH state.clock (by omega)).2 (expsWeight program) program state rfl rfl
                | thunkOp operation =>
                  cases operation with
                  | forceThunk =>
                    apply evaluate_force_step trace args source argsIH
                    intro state bound
                    apply exprIH [appUnit (.var .none 0)] state (by omega)
                    have h := appUnit_var_weight
                    simp only [expsWeight, expWeight] at measure
                    simp only [appUnit, expsWeight, expWeight] at h ⊢
                    omega
                  | allocThunk mode => exact ordinary _ (by simp) (by simp)
                  | updateThunk mode => exact ordinary _ (by simp) (by simp)
                | label index => exact ordinary _ (by simp) (by simp)
                | ffi name => exact ordinary _ (by simp) (by simp)
                | intOp operation => exact ordinary _ (by simp) (by simp)
                | wordOp operation => exact ordinary _ (by simp) (by simp)
                | blockOp operation => exact ordinary _ (by simp) (by simp)
                | globOp operation => exact ordinary _ (by simp) (by simp)
                | memOp operation => exact ordinary _ (by simp) (by simp)
  constructor
  · intro expressions env source nextEnv target result next m l index run noType length vars safe code oracle states
    exact (all source.clock).2 (expsWeight expressions) expressions source rfl rfl env nextEnv target result next
      m l index run noType length vars safe code oracle states
  · intro clock requested function nextFunction args nextArgs source target result next smaller run noType rel argsRel code oracle states
    exact (all source.clock).1 source rfl requested function nextFunction args nextArgs target result next
      run noType rel argsRel code oracle states

end Flapjack.Compiler.Backend.ClosAnnotate
