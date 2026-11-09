import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.AppSafety

/-! Mutual code and oracle safety preservation for closure evaluation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Safety preservation for closure application from one source state. -/
def AppPreservesAt {C F : Type} (source : State C F) : Prop :=
  ∀ (location : Option Nat) (function : Value) (args : List Value)
    (next : State C F) (result : Result (List Value) Value),
    evaluateApp location function args source = (result, next) → CodeSafe source → OracleSafe source →
    CodeSafe next ∧ OracleSafe next

/-- The proof-side closure evaluator and application preserve the annotation
pass's code and oracle invariants. HOL correspondence remains to be reviewed. -/
theorem evaluate_preserves_safe {C F : Type} :
    (∀ expressions, PreservesCodeOracle (C := C) (F := F) expressions) ∧
      (∀ clock, AppPreservesBelow (C := C) (F := F) clock) := by
  have all : ∀ clock : Nat,
      (∀ source : State C F, source.clock = clock → AppPreservesAt source) ∧
      (∀ weight expressions (source : State C F),
        source.clock = clock → expsWeight expressions = weight → PreservesCodeOracleAt source expressions) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ source : State C F, source.clock = clock → AppPreservesAt source := by
        intro source clockEq location function args next result run code oracle
        apply evaluateApp_preserves_safe_step location function args source next result run code oracle
        · intro body env start final result smaller bodyRun startCode startOracle
          exact (clockIH start.clock (by omega)).2 (expsWeight [body]) [body] start rfl rfl
            env result final bodyRun startCode startOracle
        · intro location function args state final result smaller appRun stateCode stateOracle
          exact (clockIH state.clock (by omega)).1 state rfl location function args final result appRun stateCode stateOracle
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ expressions (state : State C F),
              state.clock ≤ clock → expsWeight expressions < weight → PreservesCodeOracleAt state expressions := by
            intro expressions state clockLe weightLt
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions state rfl rfl
            · exact weightIH (expsWeight expressions) weightLt expressions state clockEq rfl
          have appBound : AppPreservesBelow (C := C) (F := F) (clock + 1) := by
            intro location function args state final result smaller
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ smaller) with clockLt | clockEq
            · exact (clockIH state.clock clockLt).1 state rfl location function args final result
            · exact appAll state clockEq location function args final result
          intro expressions source clockEq measure
          cases expressions with
          | nil => exact preservesCodeOracle_at evaluate_nil_preserves_safe source
          | cons first rest =>
            cases rest with
            | cons second tail =>
              apply evaluate_cons_preserves_safe_step first second tail source
              · apply exprIH [first] source (by omega)
                simp only [expsWeight] at measure ⊢; omega
              · intro state bound
                apply exprIH (second :: tail) state (by omega)
                simp only [expsWeight] at measure ⊢; omega
            | nil =>
              cases first with
              | var trace index => exact preservesCodeOracle_at (evaluate_var_preserves_safe trace index) source
              | fn name location selected arity body =>
                exact preservesCodeOracle_at (evaluate_fn_preserves_safe name location selected arity body) source
              | raise trace body =>
                apply evaluate_raise_preserves_safe_step trace body source
                apply exprIH [body] source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | tick trace body =>
                apply evaluate_tick_preserves_safe_step trace body source
                apply exprIH [body] (decClock 1 source) (by simp [decClock]; omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | call trace ticks location args =>
                apply evaluate_call_preserves_safe_step trace ticks location args source
                · apply exprIH args source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro body state smaller
                  exact (clockIH state.clock (by omega)).2 (expsWeight [body]) [body] state rfl rfl
              | «let» trace bindings body =>
                apply evaluate_let_preserves_safe_step trace bindings body source
                · apply exprIH bindings source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [body] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | letrec names location selected functions body =>
                apply evaluate_letrec_preserves_safe_step names location selected functions body source
                apply exprIH [body] source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | handle trace body handler =>
                apply evaluate_handle_preserves_safe_step trace body handler source
                · apply exprIH [body] source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [handler] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | ifThenElse trace condition yes no =>
                apply evaluate_if_preserves_safe_step trace condition yes no source
                · apply exprIH [condition] source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [yes] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [no] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | app trace location function args =>
                apply evaluate_app_preserves_safe_step trace location function args source
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
                    PreservesCodeOracleAt source [.op trace op args] := by
                  intro op notInstall notForce
                  exact evaluate_ordinaryOp_preserves_safe_step trace op args notInstall notForce source argsIH
                cases op with
                | install =>
                  apply evaluate_install_preserves_safe_step trace args source argsIH
                  intro program state smaller
                  exact (clockIH state.clock (by omega)).2 (expsWeight program) program state rfl rfl
                | thunkOp operation =>
                  cases operation with
                  | forceThunk =>
                    apply evaluate_force_preserves_safe_step trace args source argsIH
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
  · intro expressions env source result next run code oracle
    exact (all source.clock).2 (expsWeight expressions) expressions source rfl rfl env result next run code oracle
  · intro clock location function args source next result smaller run code oracle
    exact (all source.clock).1 source rfl location function args next result run code oracle

end Flapjack.Compiler.Backend.ClosAnnotate
