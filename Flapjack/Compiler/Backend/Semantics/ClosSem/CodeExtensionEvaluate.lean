module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.CodeExtensionSteps
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateCodeGrowth

@[expose] public section

/-! Simulation of closure evaluation under safe extensions of installed code. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Safe code extensions preserve every non-type-error evaluation and its
result, and remain safe after evaluation. This proof-side result is untagged
pending review of its HOL carriers and source statement. -/
theorem evaluate_codeExtension {C F : Type} :
    (∀ expressions (source : State C F), EvalCodeExtensionAt source expressions) ∧
    (∀ clock, AppCodeExtensionBelow (C := C) (F := F) clock) := by
  have all : ∀ clock : Nat,
      (∀ source : State C F, source.clock = clock → ∀ location function args target result next,
        evaluateApp location function args source = (result, next) →
        result ≠ .err (.abort .typeError) → CodeExtension source target →
        ∃ targetNext, evaluateApp location function args target = (result, targetNext) ∧ CodeExtension next targetNext) ∧
      (∀ weight expressions (source : State C F),
        source.clock = clock → expsWeight expressions = weight → EvalCodeExtensionAt source expressions) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ source : State C F, source.clock = clock → ∀ location function args target result next,
          evaluateApp location function args source = (result, next) →
          result ≠ .err (.abort .typeError) → CodeExtension source target →
          ∃ targetNext, evaluateApp location function args target = (result, targetNext) ∧ CodeExtension next targetNext := by
        intro source clockEq location function args target result next run noType states
        apply evaluateApp_codeExtension location function args source target result next run noType states
        · intro body state smaller
          exact (clockIH state.clock (by omega)).2 (expsWeight [body]) [body] state rfl rfl
        · intro location function args state target result next smaller run noType states
          exact (clockIH state.clock (by omega)).1 state rfl location function args target result next run noType states
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ expressions (state : State C F), state.clock ≤ clock →
              expsWeight expressions < weight → EvalCodeExtensionAt state expressions := by
            intro expressions state clockLe weightLt
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions state rfl rfl
            · exact weightIH (expsWeight expressions) weightLt expressions state clockEq rfl
          have appBound : AppCodeExtensionBelow (C := C) (F := F) (clock + 1) := by
            intro location function args state target result final smaller run noType states
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ smaller) with clockLt | clockEq
            · exact (clockIH state.clock clockLt).1 state rfl location function args target result final run noType states
            · exact appAll state clockEq location function args target result final run noType states
          intro expressions source clockEq measure
          cases expressions with
          | nil => exact evaluate_nil_codeExtension source
          | cons first rest =>
            cases rest with
            | cons second tail =>
              apply evaluate_cons_codeExtension first second tail source
              · apply exprIH [first] source (by omega)
                simp only [expsWeight] at measure ⊢; omega
              · intro state bound
                apply exprIH (second :: tail) state (by omega)
                simp only [expsWeight] at measure ⊢; omega
            | nil =>
              cases first with
              | var trace index => exact evaluate_var_codeExtension trace index source
              | fn name location selected arity body => exact evaluate_fn_codeExtension name location selected arity body source
              | raise trace body =>
                apply evaluate_raise_codeExtension trace body source
                apply exprIH [body] source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | tick trace body =>
                apply evaluate_tick_codeExtension trace body source
                apply exprIH [body] (decClock 1 source) (by simp [decClock]; omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | call trace ticks location args =>
                apply evaluate_call_codeExtension trace ticks location args source
                · apply exprIH args source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro body state smaller
                  exact (clockIH state.clock (by omega)).2 (expsWeight [body]) [body] state rfl rfl
              | «let» trace bindings body =>
                apply evaluate_let_codeExtension trace bindings body source
                · apply exprIH bindings source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [body] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | letrec names location selected functions body =>
                apply evaluate_letrec_codeExtension names location selected functions body source
                apply exprIH [body] source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | handle trace body handler =>
                apply evaluate_handle_codeExtension trace body handler source
                · apply exprIH [body] source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [handler] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | ifThenElse trace condition yes no =>
                apply evaluate_if_codeExtension trace condition yes no source
                · apply exprIH [condition] source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [yes] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [no] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | app trace location function args =>
                apply evaluate_app_codeExtension trace location function args source
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
                    EvalCodeExtensionAt source [.op trace op args] := by
                  intro op notInstall notForce
                  exact evaluate_ordinaryOp_codeExtension trace op args notInstall notForce source argsIH
                cases op with
                | install =>
                  apply evaluate_install_codeExtension trace args source argsIH
                  intro program state smaller
                  exact (clockIH state.clock (by omega)).2 (expsWeight program) program state rfl rfl
                | thunkOp operation =>
                  cases operation with
                  | forceThunk =>
                    apply evaluate_force_codeExtension trace args source argsIH
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
  · intro expressions source
    exact (all source.clock).2 (expsWeight expressions) expressions source rfl rfl
  · intro clock location function args source target result next smaller run noType states
    exact (all source.clock).1 source rfl location function args target result next run noType states

end Flapjack.Compiler.Backend.ClosSem
