module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateEventsControl
public import Flapjack.Misc.ClockWeightInduction

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section

/-! Event-prefix preservation for the proof-side closure evaluator. The
evaluator and its carriers await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Evaluation and closure application extend the initial FFI event trace. -/
theorem evaluate_ioEvents_prefix {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List Value) (state final : State C F)
      (result : Result (List Value) Value), evaluate expressions env state = (result, final) →
      state.ffi.ioEvents <+: final.ffi.ioEvents) ∧
    (∀ (location : Option Nat) (function : Value) (args : List Value) (state final : State C F)
      (result : Result (List Value) Value), evaluateApp location function args state = (result, final) →
      state.ffi.ioEvents <+: final.ffi.ioEvents) := by
  have parts := clockWeightAppInduction (α := List ClosLang.Exp)
    (β := Option Nat × Value × List Value) (σ := State C F) (·.clock) expsWeight
    (motiveE := fun expressions state => ∀ env final result,
      evaluate expressions env state = (result, final) → state.ffi.ioEvents <+: final.ffi.ioEvents)
    (motiveA := fun b state => ∀ final result,
      evaluateApp b.1 b.2.1 b.2.2 state = (result, final) →
      state.ffi.ioEvents <+: final.ffi.ioEvents) ?_ ?_
  · refine ⟨?_, ?_⟩
    · intro expressions env state final result run
      exact parts.1 expressions state env final result run
    · intro location function args state final result run
      exact parts.2 (location, function, args) state final result run
  · intro b s bodyIH appIH
    obtain ⟨location, function, args⟩ := b
    intro final result run
    apply evaluateApp_ioEvents_step location function args s final result ?_ ?_ run
    · intro body env start last bodyResult smaller bodyRun
      exact bodyIH [body] start smaller env last bodyResult bodyRun
    · intro value remaining start last appResult smaller appRun
      exact appIH (location, value, remaining) start smaller last appResult appRun
  · intro expressions state exprIH₀ smaller₀ appBound₀
    have exprIH := fun (es : List ClosLang.Exp) (env : List Value) (s final : State C F)
        (result : Result (List Value) Value) h1 h2 run =>
      exprIH₀ es s h1 h2 env final result run
    have smaller := fun (es : List ClosLang.Exp) (env : List Value) (s final : State C F)
        (result : Result (List Value) Value) h1 run =>
      smaller₀ es s h1 env final result run
    have appBound := fun (location : Option Nat) (function : Value) (args : List Value)
        (s final : State C F) (result : Result (List Value) Value) h run =>
      appBound₀ (location, function, args) s h final result run
    intro env final result run
    cases expressions with
    | nil =>
      simp [evaluate] at run
      rcases run with ⟨rfl, rfl⟩
      exact List.prefix_refl _
    | cons first rest =>
      cases rest with
      | cons second tail =>
        apply evaluate_cons_ioEvents_step first (second :: tail) env state final result ?_ ?_ run
        · intro last headResult headRun
          apply exprIH [first] env state last headResult (by omega) ?_ headRun
          simp only [expsWeight] at ⊢; omega
        · intro start last tailResult bound tailRun
          apply exprIH (second :: tail) env start last tailResult (by omega) ?_ tailRun
          simp only [expsWeight] at ⊢; omega
      | nil =>
        cases first with
        | var trace index =>
          rw [evaluate] at run
          split at run <;> simp at run
          all_goals rcases run with ⟨rfl, rfl⟩
          all_goals exact List.prefix_refl _
        | fn name location selected arity body =>
          rw [evaluate.eq_def] at run
          dsimp only at run
          repeat' split at run <;> simp_all
        | raise trace body =>
          apply evaluate_raise_ioEvents_step trace body env state final result ?_ run
          intro last bodyResult bodyRun
          apply exprIH [body] env state last bodyResult (by omega) ?_ bodyRun
          simp only [expsWeight, expWeight] at ⊢; omega
        | tick trace body =>
          apply evaluate_tick_ioEvents_step trace body env state final result ?_ run
          intro start last bodyResult bound bodyRun
          exact smaller [body] env start last bodyResult (by omega) bodyRun
        | call trace ticks location args =>
          apply evaluate_call_ioEvents_step trace ticks location args env state final result ?_ ?_
            run
          · intro last argResult argRun
            apply exprIH args env state last argResult (by omega) ?_ argRun
            simp only [expsWeight, expWeight] at ⊢; omega
          · intro body bodyEnv start last bodyResult bound bodyRun
            exact smaller [body] bodyEnv start last bodyResult (by omega) bodyRun
        | «let» trace bindings body =>
          apply evaluate_let_ioEvents_step trace bindings body env state final result ?_ ?_ run
          · intro last bindingResult bindingRun
            apply exprIH bindings env state last bindingResult (by omega) ?_ bindingRun
            simp only [expsWeight, expWeight] at ⊢; omega
          · intro bodyEnv start last bodyResult bound bodyRun
            apply exprIH [body] bodyEnv start last bodyResult (by omega) ?_ bodyRun
            simp only [expsWeight, expWeight] at ⊢; omega
        | letrec names location selected functions body =>
          apply evaluate_letrec_ioEvents_step names location selected functions body env state final
            result ?_ run
          intro bodyEnv bodyRun
          apply exprIH [body] bodyEnv state final result (by omega) ?_ bodyRun
          simp only [expsWeight, expWeight] at ⊢; omega
        | handle trace body handler =>
          apply evaluate_handle_ioEvents_step trace body handler env state final result ?_ ?_ run
          · intro last bodyResult bodyRun
            apply exprIH [body] env state last bodyResult (by omega) ?_ bodyRun
            simp only [expsWeight, expWeight] at ⊢; omega
          · intro value start last handlerResult bound handlerRun
            apply exprIH [handler] (value :: env) start last handlerResult (by omega) ?_ handlerRun
            simp only [expsWeight, expWeight] at ⊢; omega
        | ifThenElse trace condition yes no =>
          apply evaluate_if_ioEvents_step trace condition yes no env state final result ?_ ?_ run
          · intro last testResult testRun
            apply exprIH [condition] env state last testResult (by omega) ?_ testRun
            simp only [expsWeight, expWeight] at ⊢; omega
          · intro choice start last branchResult bound branchRun
            cases choice with
            | false =>
              apply exprIH [no] env start last branchResult (by omega) ?_ branchRun
              simp only [expsWeight, expWeight] at ⊢; omega
            | true =>
              apply exprIH [yes] env start last branchResult (by omega) ?_ branchRun
              simp only [expsWeight, expWeight] at ⊢; omega
        | app trace location function args =>
          apply evaluate_app_ioEvents_step trace location function args env state final result ?_ ?_
            ?_ run
          · intro last argResult argRun
            apply exprIH args env state last argResult (by omega) ?_ argRun
            simp only [expsWeight, expWeight] at ⊢; omega
          · intro start last functionResult bound functionRun
            apply exprIH [function] env start last functionResult (by omega) ?_ functionRun
            simp only [expsWeight, expWeight] at ⊢; omega
          · intro value arguments start last appResult bound appRun
            exact appBound location value arguments start last appResult (by omega) appRun
        | op trace op args =>
          have argsSmaller : expsWeight args < expsWeight [.op trace op args] := by
            have h := opWeight_gt trace op args
            simp only [expsWeight] at ⊢
            omega
          have argsIH : ∀ (last : State C F) (argResult : Result (List Value) Value),
              evaluate args env state = (argResult, last) → state.ffi.ioEvents <+: last.ffi.ioEvents
                := by
            intro last argResult argRun
            exact exprIH args env state last argResult (by omega) argsSmaller argRun
          have ordinary : ∀ op, op ≠ .install → op ≠ .thunkOp .forceThunk →
              evaluate [.op trace op args] env state = (result, final) → state.ffi.ioEvents <+:
                final.ffi.ioEvents := by
            intro op notInstall notForce opRun
            exact evaluate_ordinaryOp_ioEvents_step trace op args env state final result notInstall
              notForce argsIH opRun
          cases op with
          | install =>
            apply evaluate_install_ioEvents_step trace args env state final result argsIH ?_ run
            intro program start last programResult bound programRun
            exact smaller program [] start last programResult (by omega) programRun
          | thunkOp operation =>
            cases operation with
            | forceThunk =>
              apply evaluate_force_ioEvents_step trace args env state final result argsIH ?_ run
              intro value start last forceResult bound forceRun
              apply exprIH [appUnit (.var .none 0)] [value] start last forceResult (by omega) ?_
                forceRun
              have h := appUnit_var_weight
              simp only [expsWeight, expWeight] at ⊢
              simp only [appUnit, expsWeight, expWeight] at h ⊢
              omega
            | allocThunk mode => exact ordinary (.thunkOp (.allocThunk mode)) (by simp) (by simp)
                                   run
            | updateThunk mode => exact ordinary (.thunkOp (.updateThunk mode)) (by simp) (by simp)
                                    run
          | label index => exact ordinary (.label index) (by simp) (by simp) run
          | ffi name => exact ordinary (.ffi name) (by simp) (by simp) run
          | intOp operation => exact ordinary (.intOp operation) (by simp) (by simp) run
          | wordOp operation => exact ordinary (.wordOp operation) (by simp) (by simp) run
          | blockOp operation => exact ordinary (.blockOp operation) (by simp) (by simp) run
          | globOp operation => exact ordinary (.globOp operation) (by simp) (by simp) run
          | memOp operation => exact ordinary (.memOp operation) (by simp) (by simp) run

end Flapjack.Compiler.Backend.ClosSem
