import Flapjack.Compiler.Backend.ClosCall.Proofs.DirectCallImpure

/-! Expression simulation for the impure direct-call rewrite. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- The actual impure known-location traversal case composes argument and
function simulations with the extracted direct call. The body simulation and
fixed compiler-state relation are induction infrastructure; this is not the
complete HOL growing-state or oracle theorem. -/
theorem callsFuel_app_impure_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (address : Nat) (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace (some address) sourceFn sourceArgs) initial = some (out, final))
    (known : (sptLookup address final.1).isSome = true) (impure : ClosLang.pure sourceFn = false)
    (notAllowed : address ∉ allowed) (distinct : (g.2.map Prod.fst).Nodup)
    (argsIH : ∀ targetArgs middle, callsListFuel fuel sourceArgs initial = some (targetArgs, middle) →
      ExprsSimFuel (C := C) (F := F) fuel g allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel fuel sourceFn middle = some (targetFn, final) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceFn targetFn)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (sourceBody targetBody : ClosLang.Exp) (location : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code location sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody) :
    ExprSimFuel (C := C) (F := F) fuel g allowed (.app trace (some address) sourceFn sourceArgs) out := by
  obtain ⟨targetArgs, targetFn, middle, argsTraversal, fnTraversal, outEq⟩ :=
    callsFuel_app_impure_shape fuel trace address sourceFn sourceArgs initial final out run known impure
  intro sourceEnv targetEnv source target sourceResult sourceFinal sourceRun notType envs states
  have bindingEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0
      ((targetArgs ++ [targetFn]).map (0, ·)) := by
    apply envRelFuel_let_bindings (BackendCommon.mkCons trace 0) (targetArgs ++ [targetFn])
      (.call (BackendCommon.mkCons trace 1) targetArgs.length (address + 1)
        (ClosCall.variables .none targetArgs.length))
    simpa [outEq] using envs
  have argsEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 (targetArgs.map (0, ·)) := by
    apply envRelFuel_subset bindingEnv
    intro item member
    simp only [List.map_append, List.mem_append]
    exact Or.inl member
  have fnEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, targetFn)] := by
    apply envRelFuel_subset bindingEnv
    intro item member
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at member ⊢
    exact Or.inr member
  cases sourceArgs with
  | nil =>
    have bad : sourceResult = .err (.abort .typeError) := by
      simpa [evaluate] using congrArg Prod.fst sourceRun.symm
    exact False.elim (notType bad)
  | cons first rest =>
    rw [evaluate] at sourceRun
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate] at sourceRun
    cases sourceArgsRun : evaluate (first :: rest) sourceEnv source with
    | mk argsResult argsFinal =>
      have argsNotType : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        have : sourceResult = .err (.abort .typeError) := by
          simpa [sourceArgsRun] using congrArg Prod.fst sourceRun.symm
        exact notType this
      obtain ⟨targetArgsResult, targetArgsFinal, targetArgsRun, argsRel, argsStates, argsGrowth⟩ :=
        argsIH targetArgs middle argsTraversal sourceEnv targetEnv source target argsResult argsFinal
          sourceArgsRun argsNotType argsEnv states
      cases argsResult with
      | err error =>
        cases targetArgsResult with
        | val values => simp [resultRel] at argsRel
        | err targetError =>
          have sourceEq : sourceResult = .err error ∧ sourceFinal = argsFinal := by
            simpa [sourceArgsRun] using sourceRun.symm
          obtain ⟨rfl, rfl⟩ := sourceEq
          refine ⟨.err targetError, targetArgsFinal, ?_, argsRel, argsStates, argsGrowth⟩
          rw [outEq]
          exact evaluate_impure_rewrite_args_error trace (address + 1) targetArgs targetFn targetEnv target targetArgsFinal targetError targetArgsRun
      | val sourceValues =>
        cases targetArgsResult with
        | err error => simp [resultRel] at argsRel
        | val targetValues =>
          have valuesRel : List.Forall₂ (ValueRelFuel fuel g allowed targetArgsFinal.code) sourceValues targetValues := argsRel
          have fnEnv' : EnvRelFuel fuel g allowed targetArgsFinal.code sourceEnv targetEnv 0 [(0, targetFn)] :=
            envRelFuel_mono fnEnv (stateExtends_refl g distinct) Set.Subset.rfl argsGrowth
          cases sourceFnRun : evaluate [sourceFn] sourceEnv argsFinal with
          | mk fnResult fnFinal =>
            have fnNotType : fnResult ≠ .err (.abort .typeError) := by
              intro bad
              subst fnResult
              have : sourceResult = .err (.abort .typeError) := by
                simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using congrArg Prod.fst sourceRun.symm
              exact notType this
            obtain ⟨targetFnResult, targetFnFinal, targetFnRun, fnRel, fnStates, fnGrowth⟩ :=
              fnIH targetFn middle fnTraversal sourceEnv targetEnv argsFinal targetArgsFinal fnResult fnFinal
                sourceFnRun fnNotType fnEnv' argsStates
            cases fnResult with
            | err error =>
              cases targetFnResult with
              | val values => simp [resultRel] at fnRel
              | err targetError =>
                have sourceEq : sourceResult = .err error ∧ sourceFinal = fnFinal := by
                  simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using sourceRun.symm
                obtain ⟨rfl, rfl⟩ := sourceEq
                refine ⟨.err targetError, targetFnFinal, ?_, fnRel, fnStates, ?_⟩
                · rw [outEq]
                  exact evaluate_impure_rewrite_function_error trace (address + 1) targetArgs targetFn targetEnv
                    targetValues target targetArgsFinal targetFnFinal targetError targetArgsRun targetFnRun
                · intro key item lookup
                  exact fnGrowth key item (argsGrowth key item lookup)
            | val fnValues =>
              obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value sourceFn sourceEnv argsFinal fnFinal fnValues sourceFnRun
              cases targetFnResult with
              | err error => simp [resultRel] at fnRel
              | val targetFnValues =>
                obtain ⟨targetFnValue, rfl⟩ :=
                  evaluate_singleton_value targetFn targetEnv targetArgsFinal targetFnFinal targetFnValues targetFnRun
                have functionRel : ValueRelFuel fuel g allowed targetFnFinal.code fnValue targetFnValue := by
                  simpa [resultRel] using fnRel
                have valuesRel' : List.Forall₂ (ValueRelFuel fuel g allowed targetFnFinal.code) sourceValues targetValues :=
                  List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h (stateExtends_refl g distinct) Set.Subset.rfl fnGrowth) valuesRel
                have appRun : evaluateApp (some address) fnValue sourceValues fnFinal = (sourceResult, sourceFinal) := by
                  simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using sourceRun
                have nonempty : sourceValues ≠ [] := by
                  have len := (evaluate_length (C := NumSet × C) (F := F)).1 (first :: rest) sourceEnv source argsFinal sourceValues sourceArgsRun
                  intro empty
                  simp [empty] at len
                obtain ⟨result, finalTarget, targetRun, results, finalStates, growth⟩ :=
                  callsFuel_app_impure_full_sim fuel g allowed trace address sourceFn (first :: rest)
                    initial final middle out targetFn targetArgs targetEnv targetValues fnValue targetFnValue sourceValues
                    fnFinal target targetArgsFinal targetFnFinal sourceResult sourceFinal run known impure
                    argsTraversal fnTraversal targetArgsRun targetFnRun appRun notType nonempty functionRel valuesRel'
                    fnStates notAllowed distinct bodyIH
                refine ⟨result, finalTarget, targetRun, results, finalStates, ?_⟩
                intro key item lookup
                exact growth key item (fnGrowth key item (argsGrowth key item lookup))

end Flapjack.Compiler.Backend.ClosCall
