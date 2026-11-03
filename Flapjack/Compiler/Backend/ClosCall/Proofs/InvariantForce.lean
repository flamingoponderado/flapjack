import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantThunk
import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateForce

/-! Source-driven force-thunk simulation for direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem ClosProps SemanticPrimitivesProps

/-- Forcing related thunks simulates source evaluation, given a simulation
of the generated force application. The source state invariant supplies the
thunk payload's well-formedness; target code growth is tracked explicitly. -/
theorem runForced_invariant_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (sourceValues targetValues : List Value) (source : ClosSem.State (NumSet × C) F)
    (target : ClosSem.State C F) (sourceResult : SemanticPrimitivesHOL.Result (List Value) Value)
    (sourceFinal : ClosSem.State (NumSet × C) F)
    (run : ClosMti.runForced sourceValues source = (sourceResult, sourceFinal))
    (notType : sourceResult ≠ .err (.abort .typeError))
    (values : List.Forall₂ (ValueRelFuel fuel g allowed target.code) sourceValues targetValues)
    (sourceWf : StateWellFormedFuel fuel g allowed target.code source)
    (states : StateRelFuel fuel g allowed source target) (distinct : (g.2.map Prod.fst).Nodup)
    (forceIH : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed
      (appUnit (.var .none 0)) (appUnit (.var .none 0))) :
    ∃ targetResult targetFinal,
      ClosMti.runForced targetValues target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, target.code.lookup key = some value → targetFinal.code.lookup key = some value) := by
  have inspected := destThunk_relatedFuel states values
  cases sourceDest : destThunk sourceValues source.refs with
  | badRef =>
    have bad : sourceResult = .err (.abort .typeError) := by
      simpa [ClosMti.runForced, sourceDest] using congrArg Prod.fst run.symm
    exact False.elim (notType bad)
  | notThunk =>
    have bad : sourceResult = .err (.abort .typeError) := by
      simpa [ClosMti.runForced, sourceDest] using congrArg Prod.fst run.symm
    exact False.elim (notType bad)
  | isThunk mode sourceValue =>
    rw [sourceDest] at inspected
    cases targetDest : destThunk targetValues target.refs with
    | badRef => rw [targetDest] at inspected; cases inspected
    | notThunk => rw [targetDest] at inspected; cases inspected
    | isThunk targetMode targetValue =>
      rw [targetDest] at inspected
      cases inspected with
      | isThunk _ _ _ payloadRel =>
        cases mode with
        | evaluated =>
          have sourceEq : sourceResult = .val [sourceValue] ∧ sourceFinal = source := by
            simpa [ClosMti.runForced, sourceDest] using run.symm
          obtain ⟨rfl, rfl⟩ := sourceEq
          exact ⟨.val [targetValue], target, by simp [ClosMti.runForced, targetDest],
            .cons payloadRel .nil, states, fun _ _ h => h⟩
        | notEvaluated =>
          have payloadWf := destThunk_wellFormedFuel sourceValues source .notEvaluated sourceValue sourceWf sourceDest
          have forceEnv : EnvRelFuel fuel g allowed target.code [sourceValue] [targetValue] 0
              [(0, appUnit (.var .none 0))] := .equalLength rfl (.cons payloadRel .nil)
          cases forceRun : evaluate [appUnit (.var .none 0)] [sourceValue] source with
          | mk forceResult forceFinal =>
            have forceNotType : forceResult ≠ .err (.abort .typeError) := by
              intro bad
              subst forceResult
              have : sourceResult = .err (.abort .typeError) := by
                simpa [ClosMti.runForced, sourceDest, forceRun] using congrArg Prod.fst run.symm
              exact notType this
            obtain ⟨targetForceResult, targetForceFinal, targetForceRun, forceRel, forceStates, growth⟩ :=
              forceIH [sourceValue] [targetValue] source target forceResult forceFinal forceRun forceNotType forceEnv
                (.cons payloadWf .nil) sourceWf states
            cases forceResult with
            | err error =>
              cases targetForceResult with
              | val values => simp [resultRel] at forceRel
              | err targetError =>
                have sourceEq : sourceResult = .err error ∧ sourceFinal = forceFinal := by
                  simpa [ClosMti.runForced, sourceDest, forceRun] using run.symm
                obtain ⟨rfl, rfl⟩ := sourceEq
                exact ⟨.err targetError, targetForceFinal,
                  by simp [ClosMti.runForced, targetDest, targetForceRun], forceRel, forceStates, growth⟩
            | val forced =>
              cases targetForceResult with
              | err error => simp [resultRel] at forceRel
              | val targetForced =>
                have pointers := List.Forall₂.imp
                  (fun _ _ h => valueRelFuel_mono h (stateExtends_refl g distinct) Set.Subset.rfl growth) values
                have update := updateThunk_lists_relatedFuel sourceValues targetValues forced targetForced
                  forceStates pointers forceRel
                cases sourceUpdate : updateThunk sourceValues forceFinal.refs forced with
                | none =>
                  have bad : sourceResult = .err (.abort .typeError) := by
                    simpa [ClosMti.runForced, sourceDest, forceRun, sourceUpdate] using congrArg Prod.fst run.symm
                  exact False.elim (notType bad)
                | some sourceRefs =>
                  cases targetUpdate : updateThunk targetValues targetForceFinal.refs targetForced with
                  | none =>
                    have impossible := update.1 targetUpdate
                    rw [sourceUpdate] at impossible
                    contradiction
                  | some targetRefs =>
                    obtain ⟨sourceRefs', sourceUpdate', finalStates⟩ := update.2 targetRefs targetUpdate
                    rw [sourceUpdate] at sourceUpdate'
                    cases sourceUpdate'
                    have sourceEq : sourceResult = .val forced ∧ sourceFinal = { forceFinal with refs := sourceRefs } := by
                      simpa [ClosMti.runForced, sourceDest, forceRun, sourceUpdate] using run.symm
                    obtain ⟨rfl, rfl⟩ := sourceEq
                    exact ⟨.val targetForced, { targetForceFinal with refs := targetRefs },
                      by simp [ClosMti.runForced, targetDest, targetForceRun, targetUpdate],
                      forceRel, finalStates, growth⟩

/-- Force-thunk expressions simulate when their argument lists preserve the
source invariant and the generated force application simulates. This is a
conditional Lean-side case, not the complete pass correctness theorem. -/
theorem exprSimFuelInvariant_force {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (sourceArgs targetArgs : List ClosLang.Exp)
    (distinct : (g.2.map Prod.fst).Nodup)
    (argsIH : ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed sourceArgs targetArgs)
    (argsWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate sourceArgs env state))
    (forceIH : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed
      (appUnit (.var .none 0)) (appUnit (.var .none 0))) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed
      (.op trace (.thunkOp .forceThunk) sourceArgs) (.op trace (.thunkOp .forceThunk) targetArgs) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf sourceWf states
  have argsEnv := envRelFuel_op_args trace (.thunkOp .forceThunk) targetArgs envs
  rw [ClosMti.evaluate_force_eq] at run
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult argsFinal =>
    have argsNotType : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have : sourceResult = .err (.abort .typeError) := by
        simpa [argsRun] using congrArg Prod.fst run.symm
      exact notType this
    obtain ⟨targetArgsResult, targetArgsFinal, targetArgsRun, argsRel, argsStates, argsGrowth⟩ :=
      argsIH sourceEnv targetEnv source target argsResult argsFinal argsRun argsNotType argsEnv envWf sourceWf states
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val values => simp [resultRel] at argsRel
      | err targetError =>
        have sourceEq : sourceResult = .err error ∧ sourceFinal = argsFinal := by simpa [argsRun] using run.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨.err targetError, targetArgsFinal, ?_, argsRel, argsStates, argsGrowth⟩
        simp [ClosMti.evaluate_force_eq, targetArgsRun]
    | val sourceValues =>
      cases targetArgsResult with
      | err error => simp [resultRel] at argsRel
      | val targetValues =>
        have nextWf : StateWellFormedFuel fuel g allowed targetArgsFinal.code argsFinal := by
          have well := argsWf target.code sourceEnv source envWf sourceWf
          rw [argsRun] at well
          exact stateWellFormedFuel_mono well.2 (stateExtends_refl g distinct) Set.Subset.rfl argsGrowth
        have forceRun : ClosMti.runForced sourceValues argsFinal = (sourceResult, sourceFinal) := by
          simpa [argsRun] using run
        obtain ⟨targetResult, targetFinal, targetRun, results, finalStates, growth⟩ :=
          runForced_invariant_sim fuel g allowed sourceValues targetValues argsFinal targetArgsFinal sourceResult
            sourceFinal forceRun notType argsRel nextWf argsStates distinct forceIH
        refine ⟨targetResult, targetFinal, ?_, results, finalStates, ?_⟩
        · simpa [ClosMti.evaluate_force_eq, targetArgsRun] using targetRun
        · intro key item lookup
          exact growth key item (argsGrowth key item lookup)

/-- The executed traversal's force-thunk case composes the simulation of its
actual argument output with the generated force-application hypothesis. -/
theorem callsFuel_force_invariant_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.op trace (.thunkOp .forceThunk) args) initial = some (out, final))
    (distinct : (g.2.map Prod.fst).Nodup)
    (argsIH : ∀ target, callsListFuel fuel args initial = some (target, final) →
      ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed args target)
    (argsWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate args env state))
    (forceIH : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed
      (appUnit (.var .none 0)) (appUnit (.var .none 0))) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.op trace (.thunkOp .forceThunk) args) out := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := run
  exact exprSimFuelInvariant_force fuel g allowed trace args targetArgs distinct (argsIH targetArgs argsRun) argsWf forceIH

/-- The evaluator-generated force application simulates using the selected
closure-body hypotheses. Its function is a variable and its sole argument is
the unit constructor, so no additional expression induction is required. -/
theorem forceApplication_invariant_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (distinct : (g.2.map Prod.fst).Nodup)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (sourceBody targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sourceBody targetBody)
    (bodyWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (body targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, body) → targetFns[index]? = some (arity, targetBody) →
      ∀ (env : List Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
        EvalWellFormedFuel fuel g allowed code (evaluate [body] env state)) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed
      (appUnit (.var .none 0)) (appUnit (.var .none 0)) := by
  let unitExp : ClosLang.Exp := .op .none (.blockOp (.cons 0)) []
  have nilSim : ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed [] [] :=
    exprsSimFuelInvariant_of_forall₂ fuel g allowed distinct .nil
  have unitSim : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed unitExp unitExp := by
    exact exprSimFuelInvariant_ordinaryOp fuel g allowed .none (.blockOp (.cons 0)) [] [] (by simp) (by simp) nilSim
  have unitWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (env : List Value)
      (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate [unitExp] env state) := by
    intro code env state _ stateWf
    exact evaluate_ordinaryOp_wellFormedFuel .none (.blockOp (.cons 0)) [] env state (by simp) (by simp)
      (evaluate_nil_wellFormedFuel env state stateWf)
  have argsSim : ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed [unitExp] [unitExp] :=
    exprsSimFuelInvariant_of_forall₂ fuel g allowed distinct (.cons ⟨unitSim, unitWf⟩ .nil)
  have argsWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (env : List Value)
      (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate [unitExp] env state) := unitWf
  have fnSim : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.var .none 0) (.var .none 0) :=
    exprSimFuel_to_invariant (exprSimFuel_var fuel g allowed .none 0)
  have fnWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (env : List Value)
      (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate [.var .none 0] env state) := by
    intro code env state envWf stateWf
    exact evaluate_var_state_wellFormedFuel .none 0 env state envWf stateWf
  simpa [appUnit, unitExp] using
    exprSimFuelInvariant_app_invariant_bodies fuel g allowed .none none (.var .none 0) (.var .none 0)
      [unitExp] [unitExp] rfl distinct argsSim argsWf fnSim fnWf bodyIH bodyWf

/-- The actual force traversal uses the derived generated-application
simulation, assuming related closure-body simulation and well-formedness. -/
theorem callsFuel_force_invariant_bodies_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.op trace (.thunkOp .forceThunk) args) initial = some (out, final))
    (distinct : (g.2.map Prod.fst).Nodup)
    (argsIH : ∀ target, callsListFuel fuel args initial = some (target, final) →
      ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed args target)
    (argsWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate args env state))
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (sourceBody targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sourceBody targetBody)
    (bodyWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (body targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, body) → targetFns[index]? = some (arity, targetBody) →
      ∀ (env : List Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
        EvalWellFormedFuel fuel g allowed code (evaluate [body] env state)) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.op trace (.thunkOp .forceThunk) args) out := by
  exact callsFuel_force_invariant_sim fuel g allowed trace args initial final out run distinct argsIH argsWf
    (forceApplication_invariant_sim fuel g allowed distinct bodyIH bodyWf)

end Flapjack.Compiler.Backend.ClosCall
