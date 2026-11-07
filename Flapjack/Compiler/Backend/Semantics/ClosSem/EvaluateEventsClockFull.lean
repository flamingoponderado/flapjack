import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateEventsClockApp

/-! Clock-monotone event traces for the proof-side closure evaluator. The
evaluator and its state carriers await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Adding clock to evaluation or application extends its FFI event trace. -/
theorem evaluate_addClock_ioEvents_prefix {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List Value) (state : State C F) (extra : Nat),
      (evaluate expressions env state).2.ffi.ioEvents <+:
        (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents) ∧
    (∀ (location : Option Nat) (function : Value) (args : List Value) (state : State C F) (extra : Nat),
      (evaluateApp location function args state).2.ffi.ioEvents <+:
        (evaluateApp location function args { state with clock := state.clock + extra }).2.ffi.ioEvents) := by
  have all : ∀ clock : Nat,
      (∀ (location : Option Nat) (function : Value) (args : List Value) (state : State C F) (extra : Nat),
        state.clock = clock → (evaluateApp location function args state).2.ffi.ioEvents <+:
          (evaluateApp location function args { state with clock := state.clock + extra }).2.ffi.ioEvents) ∧
      (∀ (weight : Nat) (expressions : List ClosLang.Exp) (env : List Value) (state : State C F) (extra : Nat),
        state.clock = clock → expsWeight expressions = weight → (evaluate expressions env state).2.ffi.ioEvents <+:
          (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ (location : Option Nat) (function : Value) (args : List Value) (state : State C F) (extra : Nat),
          state.clock = clock → (evaluateApp location function args state).2.ffi.ioEvents <+:
            (evaluateApp location function args { state with clock := state.clock + extra }).2.ffi.ioEvents := by
        intro location function args state extra stateClock
        apply evaluateApp_addClock_ioEvents_step location function args state extra ?_ ?_
        · intro body env start smaller
          exact (clockIH start.clock (by omega)).2 (expsWeight [body]) [body] env start extra rfl rfl
        · intro value remaining start smaller
          exact (clockIH start.clock (by omega)).1 location value remaining start extra rfl
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ (expressions : List ClosLang.Exp) (env : List Value) (state : State C F) (extra : Nat),
              state.clock ≤ clock → expsWeight expressions < weight → (evaluate expressions env state).2.ffi.ioEvents <+:
                (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
            intro expressions env state extra clockLe weightLt
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions env state extra rfl rfl
            · exact weightIH (expsWeight expressions) weightLt expressions env state extra clockEq rfl
          have smaller : ∀ (expressions : List ClosLang.Exp) (env : List Value) (state : State C F) (extra : Nat),
              state.clock < clock → (evaluate expressions env state).2.ffi.ioEvents <+:
                (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
            intro expressions env state extra clockLt
            exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions env state extra rfl rfl
          have appBound : ∀ (location : Option Nat) (function : Value) (args : List Value) (state : State C F) (extra : Nat),
              state.clock ≤ clock → (evaluateApp location function args state).2.ffi.ioEvents <+:
                (evaluateApp location function args { state with clock := state.clock + extra }).2.ffi.ioEvents := by
            intro location function args state extra clockLe
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).1 location function args state extra rfl
            · exact appAll location function args state extra clockEq
          intro expressions env state extra stateClock measure
          cases expressions with
          | nil => simp [evaluate]
          | cons first rest =>
            cases rest with
            | cons second tail =>
              apply evaluate_cons_addClock_ioEvents_step first (second :: tail) env state extra ?_ ?_
              · apply exprIH [first] env state extra (by omega) ?_
                simp only [expsWeight] at measure ⊢; omega
              · intro start bound
                apply exprIH (second :: tail) env start extra (by omega) ?_
                simp only [expsWeight] at measure ⊢; omega
            | nil =>
              cases first with
              | var trace index =>
                cases run : evaluate [.var trace index] env state with
                | mk result final =>
                  have shifted := evaluate_var_addClock trace index env state final result extra run
                  simp [shifted]
              | fn name location selected arity body =>
                cases run : evaluate [.fn name location selected arity body] env state with
                | mk result final =>
                  have shifted := evaluate_fn_addClock name location selected arity body env state final result extra run
                  simp [shifted]
              | raise trace body =>
                apply evaluate_raise_addClock_ioEvents_step trace body env state extra ?_
                apply exprIH [body] env state extra (by omega) ?_
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | tick trace body =>
                apply evaluate_tick_addClock_ioEvents_step trace body env state extra ?_
                intro start bound
                exact smaller [body] env start extra (by omega)
              | call trace ticks location args =>
                apply evaluate_call_addClock_ioEvents_step trace ticks location args env state extra ?_ ?_
                · apply exprIH args env state extra (by omega) ?_
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro body bodyEnv start bound
                  exact smaller [body] bodyEnv start extra (by omega)
              | «let» trace bindings body =>
                apply evaluate_let_addClock_ioEvents_step trace bindings body env state extra ?_ ?_
                · apply exprIH bindings env state extra (by omega) ?_
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro bodyEnv start bound
                  apply exprIH [body] bodyEnv start extra (by omega) ?_
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | letrec names location selected functions body =>
                apply evaluate_letrec_addClock_ioEvents_step names location selected functions body env state extra ?_
                intro bodyEnv
                apply exprIH [body] bodyEnv state extra (by omega) ?_
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | handle trace body handler =>
                apply evaluate_handle_addClock_ioEvents_step trace body handler env state extra ?_ ?_
                · apply exprIH [body] env state extra (by omega) ?_
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro value start bound
                  apply exprIH [handler] (value :: env) start extra (by omega) ?_
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | ifThenElse trace condition yes no =>
                apply evaluate_if_addClock_ioEvents_step trace condition yes no env state extra ?_ ?_
                · apply exprIH [condition] env state extra (by omega) ?_
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro choice start bound
                  cases choice with
                  | false =>
                    apply exprIH [no] env start extra (by omega) ?_
                    simp only [expsWeight, expWeight] at measure ⊢; omega
                  | true =>
                    apply exprIH [yes] env start extra (by omega) ?_
                    simp only [expsWeight, expWeight] at measure ⊢; omega
              | app trace location function args =>
                apply evaluate_app_addClock_ioEvents_step trace location function args env state extra ?_ ?_ ?_
                · apply exprIH args env state extra (by omega) ?_
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro start bound
                  apply exprIH [function] env start extra (by omega) ?_
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro value arguments start bound
                  exact appBound location value arguments start extra (by omega)
              | op trace op args =>
                have argsSmaller : expsWeight args < weight := by
                  have h := opWeight_gt trace op args
                  simp only [expsWeight] at measure
                  omega
                have argsIH : (evaluate args env state).2.ffi.ioEvents <+:
                    (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents :=
                  exprIH args env state extra (by omega) argsSmaller
                have ordinary : ∀ op, op ≠ .install → op ≠ .thunkOp .forceThunk →
                    (evaluate [.op trace op args] env state).2.ffi.ioEvents <+:
                      (evaluate [.op trace op args] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
                  intro op notInstall notForce
                  exact evaluate_ordinaryOp_addClock_ioEvents_step trace op args env state extra notInstall notForce argsIH
                cases op with
                | install =>
                  apply evaluate_install_addClock_ioEvents_step trace args env state extra argsIH ?_
                  intro program start bound
                  exact smaller program [] start extra (by omega)
                | thunkOp operation =>
                  cases operation with
                  | forceThunk =>
                    apply evaluate_force_addClock_ioEvents_step trace args env state extra argsIH ?_
                    intro value start bound
                    apply exprIH [appUnit (.var .none 0)] [value] start extra (by omega) ?_
                    have h := appUnit_var_weight
                    simp only [expsWeight, expWeight] at measure
                    simp only [appUnit, expsWeight, expWeight] at h ⊢
                    omega
                  | allocThunk mode => exact ordinary (.thunkOp (.allocThunk mode)) (by simp) (by simp)
                  | updateThunk mode => exact ordinary (.thunkOp (.updateThunk mode)) (by simp) (by simp)
                | label index => exact ordinary (.label index) (by simp) (by simp)
                | ffi name => exact ordinary (.ffi name) (by simp) (by simp)
                | intOp operation => exact ordinary (.intOp operation) (by simp) (by simp)
                | wordOp operation => exact ordinary (.wordOp operation) (by simp) (by simp)
                | blockOp operation => exact ordinary (.blockOp operation) (by simp) (by simp)
                | globOp operation => exact ordinary (.globOp operation) (by simp) (by simp)
                | memOp operation => exact ordinary (.memOp operation) (by simp) (by simp)
  constructor
  · intro expressions env state extra
    exact (all state.clock).2 (expsWeight expressions) expressions env state extra rfl rfl
  · intro location function args state extra
    exact (all state.clock).1 location function args state extra rfl

/-- Initial-state traces are monotone in the supplied clock. -/
theorem evaluate_initial_ioEvents_mono {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C) (compiler : Compiler C)
    (program : List ClosLang.Exp) (k l : Nat) (bound : k ≤ l) :
    (evaluate program [] (initialState ffi maxApp code oracle compiler k)).2.ffi.ioEvents <+:
      (evaluate program [] (initialState ffi maxApp code oracle compiler l)).2.ffi.ioEvents := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bound
  simpa [initialState] using evaluate_addClock_ioEvents_prefix.1 program []
    (initialState ffi maxApp code oracle compiler k) extra

end Flapjack.Compiler.Backend.ClosSem
