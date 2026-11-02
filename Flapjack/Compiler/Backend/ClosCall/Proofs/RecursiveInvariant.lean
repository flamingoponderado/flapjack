import Flapjack.Compiler.Backend.ClosCall.Proofs.FunctionInvariant

/-! Direct-call invariants for mutually recursive function groups. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

private theorem callsListSource_arities (trace : BackendCommon.Tra) (index loc : Nat)
    (fns : List (Nat × ClosLang.Exp)) :
    (callsListSource trace index loc fns).map Prod.fst = fns.map Prod.fst := by
  induction fns generalizing index loc with
  | nil => rfl
  | cons fn rest ih =>
    obtain ⟨arity, body⟩ := fn
    simp [callsListSource, ih]

/-- Both extracted and retained groups preserve every function arity. -/
theorem recClosureRelFuel_arities (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (sourceFns targetFns : List (Nat × ClosLang.Exp))
    (related : recClosureRelFuel fuel g allowed code loc sourceFns targetFns) :
    targetFns.map Prod.fst = sourceFns.map Prod.fst := by
  obtain ⟨initial, _, _, _, _, bodies, afterProbe, probe, alternatives⟩ := related
  rcases alternatives with ⟨_, ⟨trace, index, rfl⟩, _⟩ |
      ⟨_, openBodies, afterOpen, openRun, rfl, _⟩
  · exact callsListSource_arities trace index loc sourceFns
  · have length := callsListBounded_length fuel (sourceFns.map Prod.snd) initial afterOpen openBodies openRun
    apply List.map_fst_zip
    simpa using Nat.le_of_eq length.symm

/-- An environment sufficient for a recursive binding is sufficient for
each of its function bodies after the recursive closures are bound. -/
theorem envRelFuel_letrec_fns {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    (names : List Basis.Pure.MlString.MlString) (loc : Nat)
    (fns : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv 0
      [(0, .letrec names (some loc) none fns body)]) :
    EnvRelFuel fuel g allowed code sourceEnv targetEnv fns.length fns := by
  apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
  have h := (envRelFuel_iff _ _ _ _ _ _ _ _).mp related
  unfold envRel at h ⊢
  by_cases same : sourceEnv.length = targetEnv.length
  · simpa [same] using h
  simp only [same, ↓reduceIte] at h ⊢
  intro x ⟨fn, member, free⟩
  apply h x
  simp only [List.mem_singleton, exists_eq_left, Nat.zero_add,
    ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp, or_false]
  left
  apply (freeVarFuns_exists x fns.length fns).mpr
  refine ⟨fn, member, ?_⟩
  simpa [ClosProps.freeVar, ClosProps.freeVars, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using free

/-- A related recursive group yields pointwise-related closure values at
every index. -/
theorem recClosureRelFuel_values {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    {loc : Nat} {sourceFns targetFns : List (Nat × ClosLang.Exp)}
    (closure : recClosureRelFuel fuel g allowed code loc sourceFns targetFns)
    (envs : EnvRelFuel fuel g allowed code sourceEnv targetEnv targetFns.length targetFns) :
    List.Forall₂ (ValueRelFuel fuel g allowed code)
      ((List.range sourceFns.length).map (fun i => .recclosure (some loc) [] sourceEnv sourceFns i))
      ((List.range targetFns.length).map (fun i => .recclosure (some loc) [] targetEnv targetFns i)) := by
  have length := recClosureRelFuel_length fuel g allowed code loc sourceFns targetFns closure
  rw [length]
  generalize List.range sourceFns.length = indices
  induction indices with
  | nil => exact .nil
  | cons i rest ih => exact .cons (.recclosure closure .nil envs) ih

/-- The body of a recursive binding accesses the outer environment after the
recursive function slots. -/
theorem envRelFuel_letrec_body_outer {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    (names : List Basis.Pure.MlString.MlString) (loc : Nat)
    (fns : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv 0
      [(0, .letrec names (some loc) none fns body)]) :
    EnvRelFuel fuel g allowed code sourceEnv targetEnv fns.length [(0, body)] := by
  apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
  have h := (envRelFuel_iff _ _ _ _ _ _ _ _).mp related
  unfold envRel at h ⊢
  by_cases same : sourceEnv.length = targetEnv.length
  · simpa [same] using h
  simp only [same, ↓reduceIte] at h ⊢
  intro x used
  apply h x
  simp only [List.mem_singleton, exists_eq_left, Nat.zero_add] at used ⊢
  simp only [ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp, or_false] at used ⊢
  exact Or.inr (by simpa [Nat.add_comm] using used)

/-- Related recursive closures can be prepended before evaluating the body. -/
theorem envRelFuel_letrec_enter {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    (names : List Basis.Pure.MlString.MlString) (loc : Nat)
    (sourceFns targetFns : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (closure : recClosureRelFuel fuel g allowed code loc sourceFns targetFns)
    (envs : EnvRelFuel fuel g allowed code sourceEnv targetEnv 0
      [(0, .letrec names (some loc) none targetFns body)]) :
    EnvRelFuel fuel g allowed code
      ((List.range sourceFns.length).map (fun i => .recclosure (some loc) [] sourceEnv sourceFns i) ++ sourceEnv)
      ((List.range targetFns.length).map (fun i => .recclosure (some loc) [] targetEnv targetFns i) ++ targetEnv)
      0 [(0, body)] := by
  have captured := envRelFuel_letrec_fns names loc targetFns body envs
  have values := recClosureRelFuel_values closure captured
  have outer := envRelFuel_letrec_body_outer names loc targetFns body envs
  have length := recClosureRelFuel_length fuel g allowed code loc sourceFns targetFns closure
  apply envRelFuel_prepend values
  simpa [length] using outer

/-- Recursive binding evaluation follows the body simulation once the pass
has established the recursive-closure relation. This helper does not yet
establish the group invariant from the full enclosing HOL hypotheses. -/
theorem evaluate_letrec_fuel {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat)
    (sourceFns targetFns : List (Nat × ClosLang.Exp)) (sourceBody targetBody : ClosLang.Exp)
    (bodyIH : ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody)
    (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value) (sourceFinal : ClosSem.State (NumSet × C) F)
    (sourceRun : evaluate [.letrec names (some loc) none sourceFns sourceBody] sourceEnv source =
      (sourceResult, sourceFinal))
    (notType : sourceResult ≠ .err (.abort .typeError))
    (envs : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0
      [(0, .letrec names (some loc) none targetFns targetBody)])
    (states : StateRelFuel fuel g allowed source target)
    (closure : recClosureRelFuel fuel g allowed target.code loc sourceFns targetFns) :
    ∃ targetResult targetFinal,
      evaluate [.letrec names (some loc) none targetFns targetBody] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, target.code.lookup key = some value → targetFinal.code.lookup key = some value) := by
  have valid : sourceFns.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true := by
    by_contra invalid
    have bad : sourceResult = .err (.abort .typeError) := by
      simpa [evaluate, invalid] using congrArg Prod.fst sourceRun.symm
    exact notType bad
  have targetValid : targetFns.all (fun (arity, _) => arity ≤ target.maxApp && arity != 0) = true := by
    have arities := recClosureRelFuel_arities fuel g allowed target.code loc sourceFns targetFns closure
    have same := congrArg (fun xs : List Nat => xs.all (fun arity => arity ≤ source.maxApp && arity != 0)) arities
    simp only [List.all_map, Function.comp_def] at same
    rw [← states.2.2.1, same]
    exact valid
  have bodyEnv := envRelFuel_letrec_enter names loc sourceFns targetFns targetBody closure envs
  have bodyRun : evaluate [sourceBody]
      ((List.range sourceFns.length).map (fun i => .recclosure (some loc) [] sourceEnv sourceFns i) ++ sourceEnv)
      source = (sourceResult, sourceFinal) := by
    simpa [evaluate, valid] using sourceRun
  obtain ⟨result, final, targetRun, results, finalStates, growth⟩ :=
    bodyIH _ _ source target sourceResult sourceFinal bodyRun notType bodyEnv states
  refine ⟨result, final, ?_, results, finalStates, growth⟩
  simpa [evaluate, targetValid] using targetRun

/-- A closed recursive-group traversal emits stubs and establishes the group
relation when the enclosing pass invariants provide freshness, state growth,
location coverage, and inclusion of the generated code. -/
theorem callsFuel_letrec_closed_invariant (fuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (body body' : ClosLang.Exp) (initial afterBodies final g : State)
    (bodies : List ClosLang.Exp) (allowed : Set Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (bodyRun : callsListFuel fuel (fns.map Prod.snd) (insertEach loc fns.length initial) =
      some (bodies, afterBodies))
    (closed : groupClosed fns bodies)
    (continuation : callsFuel fuel body (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies) =
      some (body', final))
    (wf : recClosureWellFormed loc fns) (initialWf : wellFormed initial)
    (nestedFresh : ∀ k ∈ codeLocations (fns.map Prod.snd), k + 1 ∉ initial.2.map Prod.fst)
    (ownFresh : ∀ i, i < fns.length → 2 * i + loc + 1 ∉ initial.2.map Prod.fst)
    (growth : stateExtends (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies) g)
    (covered : groupLocationsCovered fns afterBodies allowed)
    (included : codeIncludes (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies).2 code) :
    callsFuel (fuel + 1) (.letrec names (some loc) none fns body) initial =
      some (.letrec names (some loc) none (callsList loc fns) body', final) ∧
    recClosureRelFuel fuel g allowed code loc fns (callsList loc fns) := by
  constructor
  · exact callsFuel_letrec_closedBranch fuel names (some loc) none fns body initial afterBodies final
      bodies body' bodyRun closed continuation
  · refine ⟨initial, wf, initialWf, nestedFresh, ownFresh, bodies, afterBodies, ?_, Or.inl ?_⟩
    · simp [callsListBounded, bodyRun]
    · exact ⟨closed, ⟨.none, 1, callsList_eq_source loc fns⟩, growth, covered, included⟩

/-- An open recursive-group traversal retries the original bodies and
establishes the relation for the resulting retained closures. -/
theorem callsFuel_letrec_open_invariant (fuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (body body' : ClosLang.Exp) (initial afterProbe afterRetry final g : State)
    (probeBodies retryBodies : List ClosLang.Exp) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (probe : callsListFuel fuel (fns.map Prod.snd) (insertEach loc fns.length initial) =
      some (probeBodies, afterProbe))
    (notClosed : ¬groupClosed fns probeBodies)
    (retry : callsListFuel fuel (fns.map Prod.snd) initial = some (retryBodies, afterRetry))
    (continuation : callsFuel fuel body afterRetry = some (body', final))
    (wf : recClosureWellFormed loc fns) (initialWf : wellFormed initial)
    (nestedFresh : ∀ k ∈ codeLocations (fns.map Prod.snd), k + 1 ∉ initial.2.map Prod.fst)
    (ownFresh : ∀ i, i < fns.length → 2 * i + loc + 1 ∉ initial.2.map Prod.fst)
    (growth : stateExtends afterRetry g) (covered : groupLocationsCovered fns afterRetry allowed)
    (ownAllowed : ∀ i, i < fns.length → 2 * i + loc ∈ allowed)
    (included : codeIncludes afterRetry.2 code) :
    callsFuel (fuel + 1) (.letrec names (some loc) none fns body) initial =
      some (.letrec names (some loc) none ((fns.map Prod.fst).zip retryBodies) body', final) ∧
    recClosureRelFuel fuel g allowed code loc fns ((fns.map Prod.fst).zip retryBodies) := by
  constructor
  · exact callsFuel_letrec_openBranch fuel names (some loc) none fns body initial afterProbe afterRetry final
      probeBodies retryBodies body' probe notClosed retry continuation
  · refine ⟨initial, wf, initialWf, nestedFresh, ownFresh, probeBodies, afterProbe, ?_, Or.inr ?_⟩
    · simp [callsListBounded, probe]
    · refine ⟨notClosed, retryBodies, afterRetry, ?_, rfl, growth, covered, ownAllowed, included⟩
      simp [callsListBounded, retry]

end Flapjack.Compiler.Backend.ClosCall
