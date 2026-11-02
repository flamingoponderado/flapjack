import Flapjack.Compiler.Backend.ClosCall.Proofs.InstallWellformed

/-! Well-formedness of ordinary closure primitive expressions. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL

/-- An ordinary primitive expression preserves result and state
well-formedness when evaluation of its arguments does. Install and
force-thunk are handled by their separate evaluator cases. -/
theorem evaluate_ordinaryOp_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : EvalWellFormedFuel fuel g allowed code (evaluate args env state)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.op trace op args] env state) := by
  rw [evaluate_ordinaryOp_eq trace op args env state notInstall notForce]
  cases argsRun : evaluate args env state with
  | mk argsResult argsFinal =>
    rw [argsRun] at argsIH
    cases argsResult with
    | err error => simpa [EvalWellFormedFuel] using argsIH
    | val values =>
      have primWf := doApp_result_wellFormedFuel op values.reverse argsFinal argsIH.2
        (valuesWellFormedFuel_reverse argsIH.1)
      cases primRun : doApp op values.reverse argsFinal with
      | err error =>
        rw [primRun] at primWf
        cases error <;> simpa [EvalWellFormedFuel, ResultWellFormedFuel, PrimitiveResultWellFormedFuel, primRun] using
          And.intro primWf argsIH.2
      | val pair =>
        obtain ⟨value, final⟩ := pair
        rw [primRun] at primWf
        simpa [EvalWellFormedFuel, ResultWellFormedFuel, PrimitiveResultWellFormedFuel, primRun] using
          And.intro (ValuesWellFormedFuel.cons primWf.1 .nil) primWf.2

/-- An ordinary primitive expression preserves empty auxiliary code in the
source oracle when argument evaluation preserves it. -/
theorem evaluate_ordinaryOp_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : OracleAuxEmpty (evaluate args env state).2.compileOracle) :
    OracleAuxEmpty (evaluate [.op trace op args] env state).2.compileOracle := by
  rw [evaluate_ordinaryOp_eq trace op args env state notInstall notForce]
  cases argsRun : evaluate args env state with
  | mk argsResult argsFinal =>
    rw [argsRun] at argsIH
    cases argsResult with
    | err error => exact argsIH
    | val values =>
      cases primRun : doApp op values.reverse argsFinal with
      | err error => simpa [primRun] using argsIH
      | val pair =>
        obtain ⟨value, final⟩ := pair
        simpa [primRun] using doApp_oracleAuxEmpty op values.reverse argsFinal final value argsIH primRun

/-- All primitive-expression cases preserve the bounded evaluation
invariant given the argument, install, and force-thunk induction hypotheses.
The empty-auxiliary condition is required at an install boundary. -/
theorem evaluate_op_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (argsIH : EvalWellFormedFuel fuel g allowed code (evaluate args env state))
    (oracleEmpty : ((evaluate args env state).2.compileOracle 0).2.2 = [])
    (installIH : ∀ (program : List ClosLang.Exp) (start : ClosSem.State C F),
      start.clock < state.clock → StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate program [] start))
    (forceIH : op = .thunkOp .forceThunk → ∀ (value : ClosSem.Value) (start : ClosSem.State C F),
      start.clock ≤ state.clock → ValueWellFormedFuel fuel g allowed code value → StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate [appUnit (.var .none 0)] [value] start)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.op trace op args] env state) := by
  have ordinary : ∀ op, op ≠ .install → op ≠ .thunkOp .forceThunk →
      EvalWellFormedFuel fuel g allowed code (evaluate [.op trace op args] env state) := by
    intro op notInstall notForce
    exact evaluate_ordinaryOp_wellFormedFuel trace op args env state notInstall notForce argsIH
  cases op with
  | install => exact evaluate_install_wellFormedFuel trace args env state argsIH oracleEmpty installIH
  | thunkOp operation =>
    cases operation with
    | forceThunk => exact evaluate_force_wellFormedFuel trace args env state argsIH (forceIH rfl)
    | allocThunk mode => exact ordinary _ (by simp) (by simp)
    | updateThunk mode => exact ordinary _ (by simp) (by simp)
  | label | ffi | intOp | wordOp | blockOp | globOp | memOp => exact ordinary _ (by simp) (by simp)

/-- All primitive-expression cases preserve the empty-auxiliary oracle
condition under their argument, install, and force-thunk induction hypotheses. -/
theorem evaluate_op_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (argsIH : OracleAuxEmpty (evaluate args env state).2.compileOracle)
    (installIH : ∀ (program : List ClosLang.Exp) (start : ClosSem.State C F),
      start.clock < state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate program [] start).2.compileOracle)
    (forceIH : op = .thunkOp .forceThunk → ∀ (value : ClosSem.Value) (start : ClosSem.State C F),
      start.clock ≤ state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate [appUnit (.var .none 0)] [value] start).2.compileOracle) :
    OracleAuxEmpty (evaluate [.op trace op args] env state).2.compileOracle := by
  have ordinary : ∀ op, op ≠ .install → op ≠ .thunkOp .forceThunk →
      OracleAuxEmpty (evaluate [.op trace op args] env state).2.compileOracle := by
    intro op notInstall notForce
    exact evaluate_ordinaryOp_oracleAuxEmpty trace op args env state notInstall notForce argsIH
  cases op with
  | install => exact evaluate_install_oracleAuxEmpty trace args env state argsIH installIH
  | thunkOp operation =>
    cases operation with
    | forceThunk => exact evaluate_force_oracleAuxEmpty trace args env state argsIH (forceIH rfl)
    | allocThunk mode => exact ordinary _ (by simp) (by simp)
    | updateThunk mode => exact ordinary _ (by simp) (by simp)
  | label | ffi | intOp | wordOp | blockOp | globOp | memOp => exact ordinary _ (by simp) (by simp)

end Flapjack.Compiler.Backend.ClosCall
