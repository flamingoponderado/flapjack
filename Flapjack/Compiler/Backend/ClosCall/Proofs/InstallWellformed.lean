import Flapjack.Compiler.Backend.ClosCall.Proofs.ThunkWellformed
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyCode
import Flapjack.Compiler.Backend.Semantics.ClosProps.AdjustOracle

/-! Source-state well-formedness during dynamic installation. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL

/-- Every source oracle entry has an empty auxiliary code list. This is the
specific consequence needed from the full source compiler-oracle invariant. -/
def OracleAuxEmpty {C : Type} (oracle : ClosSem.CompileOracle C) : Prop :=
  ∀ index, (oracle index).2.2 = []

/-- Shifting a source oracle preserves empty auxiliary code at every entry. -/
theorem oracleAuxEmpty_shift {C : Type} (oracle : ClosSem.CompileOracle C) (offset : Nat)
    (empty : OracleAuxEmpty oracle) : OracleAuxEmpty (holShiftSeq offset oracle) := by
  intro index
  exact empty (index + offset)

/-- A successful ordinary primitive does not change the compiler oracle. -/
theorem doApp_oracleAuxEmpty {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (empty : OracleAuxEmpty state.compileOracle)
    (run : doApp op args state = .val (value, next)) : OracleAuxEmpty next.compileOracle := by
  rw [(doApp_codeOracle op args state next value run).2]
  exact empty

/-- A rejected installation leaves the state unchanged. -/
theorem doInstall_typeError_state {C F : Type} (values : List ClosSem.Value) (state next : ClosSem.State C F)
    (run : doInstall values state = (.err (.abort .typeError), next)) : next = state := by
  classical
  unfold doInstall at run
  repeat' first | split at run | simp_all

/-- Installation never raises a closure-language exception. -/
theorem doInstall_noRaise {C F : Type} (values : List ClosSem.Value) (state next : ClosSem.State C F)
    (value : ClosSem.Value) (run : doInstall values state = (.err (.raise value), next)) : False := by
  classical
  unfold doInstall at run
  repeat' first | split at run | simp_all

/-- When the current source oracle has no auxiliary code, installation
preserves the bounded source-state invariant, including the timeout case.
The oracle condition is a local consequence required from the larger compiler
invariant; this lemma does not establish that invariant. -/
theorem doInstall_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (values : List ClosSem.Value)
    (state next : ClosSem.State C F) (result : Result (List ClosLang.Exp) ClosSem.Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (oracleEmpty : (state.compileOracle 0).2.2 = [])
    (run : doInstall values state = (result, next)) :
    StateWellFormedFuel fuel g allowed code next := by
  by_cases typeError : result = .err (.abort .typeError)
  · subst result
    have same := doInstall_typeError_state values state next run
    subst next
    exact stateWf
  · obtain ⟨_, _, _, _, _, _, auxiliary, _, _, _, _, oracleRun, _, _, _, _, _, finalEq, _⟩ :=
      doInstall_nonType_parts values state next result run typeError
    have auxEmpty : auxiliary = [] := by simpa [oracleRun] using oracleEmpty
    subst auxiliary
    subst next
    simpa [StateWellFormedFuel, HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL] using stateWf

/-- Installation preserves empty auxiliary code throughout the source
oracle, including rejected and timed-out installations. -/
theorem doInstall_oracleAuxEmpty {C F : Type} (values : List ClosSem.Value)
    (state next : ClosSem.State C F) (result : Result (List ClosLang.Exp) ClosSem.Value)
    (oracleEmpty : OracleAuxEmpty state.compileOracle)
    (run : doInstall values state = (result, next)) : OracleAuxEmpty next.compileOracle := by
  by_cases typeError : result = .err (.abort .typeError)
  · subst result
    have same := doInstall_typeError_state values state next run
    subst next
    exact oracleEmpty
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, finalEq, _⟩ :=
      doInstall_nonType_parts values state next result run typeError
    subst next
    exact oracleAuxEmpty_shift state.compileOracle 1 oracleEmpty

/-- Installation preserves both the state and oracle parts of the bounded
invariant when all source oracle entries have empty auxiliary code. -/
theorem doInstall_wellFormedFuel_withOracle {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (values : List ClosSem.Value)
    (state next : ClosSem.State C F) (result : Result (List ClosLang.Exp) ClosSem.Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (oracleEmpty : OracleAuxEmpty state.compileOracle)
    (run : doInstall values state = (result, next)) :
    StateWellFormedFuel fuel g allowed code next ∧ OracleAuxEmpty next.compileOracle :=
  ⟨doInstall_wellFormedFuel values state next result stateWf (oracleEmpty 0) run,
    doInstall_oracleAuxEmpty values state next result oracleEmpty run⟩

/-- The install expression preserves empty auxiliary code in the oracle,
assuming its argument and installed-program induction hypotheses. -/
theorem evaluate_install_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (argsIH : OracleAuxEmpty (evaluate args env state).2.compileOracle)
    (bodyIH : ∀ (program : List ClosLang.Exp) (start : ClosSem.State C F),
      start.clock < state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate program [] start).2.compileOracle) :
    OracleAuxEmpty (evaluate [.op trace .install args] env state).2.compileOracle := by
  cases argsRun : evaluate args env state with
  | mk argsResult argsFinal =>
    rw [argsRun] at argsIH
    rw [evaluate, fixClock_evaluate, argsRun]
    cases argsResult with
    | err error => simpa using argsIH
    | val values =>
      dsimp only
      cases installRun : doInstall values.reverse argsFinal with
      | mk installResult installFinal =>
        have installOracle := doInstall_oracleAuxEmpty values.reverse argsFinal installFinal installResult argsIH installRun
        cases installResult with
        | err error => exact installOracle
        | val program =>
          dsimp only
          have argsBound := evaluate_clock_le args env state
          rw [argsRun] at argsBound
          dsimp only at argsBound
          have installBound := doInstall_success_clock values.reverse argsFinal installFinal program installRun
          have bodyOracle := bodyIH program installFinal (by omega) installOracle
          cases bodyRun : evaluate program [] installFinal with
          | mk result final =>
            rw [bodyRun] at bodyOracle
            cases result <;> exact bodyOracle

/-- Forcing a thunk preserves empty auxiliary code in the oracle, assuming
the corresponding argument and forced-body induction hypotheses. -/
theorem evaluate_force_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (argsIH : OracleAuxEmpty (evaluate args env state).2.compileOracle)
    (bodyIH : ∀ (value : ClosSem.Value) (start : ClosSem.State C F),
      start.clock ≤ state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate [appUnit (.var .none 0)] [value] start).2.compileOracle) :
    OracleAuxEmpty (evaluate [.op trace (.thunkOp .forceThunk) args] env state).2.compileOracle := by
  cases argsRun : evaluate args env state with
  | mk argsResult argsFinal =>
    rw [argsRun] at argsIH
    rw [evaluate, fixClock_evaluate, argsRun]
    cases argsResult with
    | err error => exact argsIH
    | val values =>
      dsimp only
      cases inspected : destThunk values argsFinal.refs with
      | badRef => exact argsIH
      | notThunk => exact argsIH
      | isThunk mode value =>
        cases mode with
        | evaluated => exact argsIH
        | notEvaluated =>
          have argsBound := evaluate_clock_le args env state
          rw [argsRun] at argsBound
          have bodyOracle := bodyIH value argsFinal argsBound argsIH
          cases bodyRun : evaluate [appUnit (.var .none 0)] [value] argsFinal with
          | mk result final =>
            rw [bodyRun] at bodyOracle
            cases result with
            | err error => simpa [bodyRun] using bodyOracle
            | val forced =>
              cases stored : updateThunk values final.refs forced <;> simpa [bodyRun, stored] using bodyOracle

/-- The final element of a nonempty list is a member of that list. -/
theorem holLast_mem_nonempty {A : Type} [Nonempty A] (values : List A) (nonempty : values ≠ []) :
    holLast values ∈ values := by
  induction values with
  | nil => contradiction
  | cons head rest ih =>
    cases rest with
    | nil => simp [holLast]
    | cons next tail =>
      rw [holLast_cons]
      simp only [List.cons_ne_nil, ↓reduceIte, List.mem_cons]
      have member := ih (by simp)
      simp only [List.mem_cons] at member
      tauto

/-- The actual installed-program continuation preserves well-formedness at
the caller-supplied compiler state and code, including the last result value.
This formulation permits those parameters to be the state and code produced
by an incremental installation. This is Flapjack-specific infrastructure. -/
theorem runInstalled_wellFormedFuel_of_actual_install {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (values : List ClosSem.Value) (source : ClosSem.State C F)
    (installedWf : StateWellFormedFuel fuel g allowed code (doInstall values source).2)
    (programIH : ∀ program installed, doInstall values source = (.val program, installed) →
      EvalWellFormedFuel fuel g allowed code (evaluate program [] installed)) :
    EvalWellFormedFuel fuel g allowed code (ClosProps.runInstalled values source) := by
  unfold ClosProps.runInstalled
  cases installRun : doInstall values source with
  | mk installResult installed =>
    rw [installRun] at installedWf
    cases installResult with
    | err error =>
      cases error with
      | raise value => exact (doInstall_noRaise values source installed value installRun).elim
      | abort reason => simpa [EvalWellFormedFuel, ResultWellFormedFuel] using installedWf
    | val program =>
      have programWf := programIH program installed installRun
      obtain ⟨_, _, _, _, _, expressions, _, _, _, _, _, _, _, _, _, _, nonempty, _, resultEq⟩ :=
        doInstall_nonType_parts values source installed (.val program) installRun (by simp)
      have programEq : program = expressions := by
        split at resultEq <;> simp_all
      have programNonempty : program ≠ [] := by simpa [programEq] using nonempty
      cases programRun : evaluate program [] installed with
      | mk result final =>
        rw [programRun] at programWf
        cases result with
        | err error => simpa [programRun] using programWf
        | val resultValues =>
          let _ : Nonempty ClosSem.Value := ⟨unitValue⟩
          have length := (evaluate_length (C := C) (F := F)).1 program [] installed final resultValues programRun
          have resultNonempty : resultValues ≠ [] := by
            intro empty
            simp [empty] at length
            exact programNonempty (List.length_eq_zero_iff.mp length.symm)
          have lastWf := valuesWellFormedFuel_mem programWf.1 (holLast_mem_nonempty resultValues resultNonempty)
          simpa [programRun, EvalWellFormedFuel, ResultWellFormedFuel] using
            And.intro (ValuesWellFormedFuel.cons lastWf .nil) programWf.2

/-- An install expression preserves well-formedness when its actual argument
result and installed continuation do so at the chosen final compiler state
and code. This is Flapjack-specific infrastructure. -/
theorem evaluate_install_wellFormedFuel_of_actual_args {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (argsWf : EvalWellFormedFuel fuel g allowed code (evaluate args env state))
    (installIH : ∀ values next, evaluate args env state = (.val values, next) →
      EvalWellFormedFuel fuel g allowed code (ClosProps.runInstalled values.reverse next)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.op trace .install args] env state) := by
  rw [ClosProps.evaluate_install_eq]
  cases argsRun : evaluate args env state with
  | mk result next =>
    rw [argsRun] at argsWf
    cases result with
    | err error => exact argsWf
    | val values => exact installIH values next argsRun

/-- Dynamic installation preserves the bounded evaluation invariant when
the current oracle's auxiliary list is empty and installed code satisfies
the recursive evaluation hypothesis. -/
theorem evaluate_install_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (argsIH : EvalWellFormedFuel fuel g allowed code (evaluate args env state))
    (oracleEmpty : ((evaluate args env state).2.compileOracle 0).2.2 = [])
    (bodyIH : ∀ (program : List ClosLang.Exp) (start : ClosSem.State C F),
      start.clock < state.clock → StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate program [] start)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.op trace .install args] env state) := by
  cases argsRun : evaluate args env state with
  | mk argsResult argsFinal =>
    rw [argsRun] at argsIH oracleEmpty
    rw [ClosProps.evaluate_install_eq, argsRun]
    cases argsResult with
    | err error => exact argsIH
    | val values =>
      have installedWf : StateWellFormedFuel fuel g allowed code (doInstall values.reverse argsFinal).2 := by
        cases installRun : doInstall values.reverse argsFinal with
        | mk result installed =>
          exact doInstall_wellFormedFuel values.reverse argsFinal installed result argsIH.2 oracleEmpty installRun
      apply runInstalled_wellFormedFuel_of_actual_install values.reverse argsFinal installedWf
      intro program installed installRun
      have argsBound := evaluate_clock_le args env state
      rw [argsRun] at argsBound
      dsimp only at argsBound
      have installBound := doInstall_success_clock values.reverse argsFinal installed program installRun
      have stateWf := doInstall_wellFormedFuel values.reverse argsFinal installed (.val program) argsIH.2 oracleEmpty installRun
      exact bodyIH program installed (by omega) stateWf

end Flapjack.Compiler.Backend.ClosCall
