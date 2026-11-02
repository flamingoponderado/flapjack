import Flapjack.Compiler.Backend.ClosCall.Proofs.ThunkWellformed
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength

/-! Source-state well-formedness during dynamic installation. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL

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

/-- The final element of a nonempty list is a member of that list. -/
private theorem holLast_mem_nonempty {A : Type} [Nonempty A] (values : List A) (nonempty : values ≠ []) :
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

/-- Dynamic installation preserves the bounded evaluation invariant when
the current oracle's auxiliary list is empty and installed code satisfies
the recursive evaluation hypothesis. -/
theorem evaluate_install_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (argsIH : EvalWellFormedFuel fuel g allowed code (evaluate args env state))
    (oracleEmpty : ((evaluate args env state).2.compileOracle 0).2.2 = [])
    (bodyIH : ∀ (program : List ClosLang.Exp) (start : ClosSem.State C F),
      StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate program [] start)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.op trace .install args] env state) := by
  cases argsRun : evaluate args env state with
  | mk argsResult argsFinal =>
    rw [argsRun] at argsIH oracleEmpty
    rw [evaluate, fixClock_evaluate, argsRun]
    cases argsResult with
    | err error => simpa [EvalWellFormedFuel] using argsIH
    | val values =>
      dsimp only
      cases installRun : doInstall values.reverse argsFinal with
      | mk installResult installFinal =>
        have installWf := doInstall_wellFormedFuel values.reverse argsFinal installFinal installResult
          argsIH.2 oracleEmpty installRun
        cases installResult with
        | err error =>
          cases error with
          | raise value => exact (doInstall_noRaise values.reverse argsFinal installFinal value installRun).elim
          | abort reason => simpa [EvalWellFormedFuel, ResultWellFormedFuel] using installWf
        | val program =>
          dsimp only
          have parts := doInstall_nonType_parts values.reverse argsFinal installFinal (.val program) installRun (by simp)
          obtain ⟨_, _, _, _, _, expressions, _, _, _, _, _, _, _, _, _, _, programNonempty, _, resultEq⟩ := parts
          have programEq : program = expressions := by
            split at resultEq <;> simp_all
          have nonempty : program ≠ [] := by simpa [programEq] using programNonempty
          have bodyWf := bodyIH program installFinal installWf
          cases bodyRun : evaluate program [] installFinal with
          | mk bodyResult bodyFinal =>
            rw [bodyRun] at bodyWf
            cases bodyResult with
            | err error => simpa [EvalWellFormedFuel] using bodyWf
            | val resultValues =>
              let _ : Nonempty ClosSem.Value := ⟨unitValue⟩
              have length := (evaluate_length (C := C) (F := F)).1 program [] installFinal bodyFinal resultValues bodyRun
              have resultNonempty : resultValues ≠ [] := by
                intro empty
                simp [empty] at length
                exact nonempty (List.length_eq_zero_iff.mp length.symm)
              have lastWf := valuesWellFormedFuel_mem bodyWf.1 (holLast_mem_nonempty resultValues resultNonempty)
              change EvalWellFormedFuel fuel g allowed code (.val [holLast resultValues], bodyFinal)
              exact ⟨.cons lastWf .nil, bodyWf.2⟩

end Flapjack.Compiler.Backend.ClosCall
