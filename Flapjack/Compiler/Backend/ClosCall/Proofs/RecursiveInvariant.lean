import Flapjack.Compiler.Backend.ClosCall.Proofs.FunctionInvariant

/-! Direct-call invariants for mutually recursive function groups. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- A source recursive binding's annotation, distinctness and label-freshness
conditions establish the corresponding group invariants. -/
theorem letrec_source_invariants (names : List Basis.Pure.MlString.MlString) (loc : Nat)
    (fns : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (initial : State)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial) :
    recClosureWellFormed loc fns ∧
      (∀ k ∈ codeLocations (fns.map Prod.snd), k + 1 ∉ initial.2.map Prod.fst) ∧
      (∀ i, i < fns.length → 2 * i + loc + 1 ∉ initial.2.map Prod.fst) := by
  let nested := codeLocations (fns.map Prod.snd)
  let own := (List.range fns.length).map (fun i => loc + 2 * i)
  have nodup : (nested ++ own ++ codeLocationsExp body).Nodup := by
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, nested, own] using distinct
  have nodupGroup : (nested ++ own).Nodup := (List.nodup_append.mp nodup).1
  have nestedNodup : nested.Nodup := (List.nodup_append.mp nodupGroup).1
  have separate := (List.nodup_append.mp nodupGroup).2.2
  have fresh' : LabelsFresh (nested ++ own ++ codeLocationsExp body) initial := by
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, nested, own] using fresh
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · apply (fnLocationSomeFuns_eq_map fns).mp
      have h : fnLocationSomeFuns fns ∧ fnLocationSomeExp body := by
        simpa [everyFnLocationSome, fnLocationSomeExp] using locations
      exact h.1
    · apply (fnVarsNoneFuns_eq_map fns).mp
      have h : fnVarsNoneFuns fns ∧ fnVarsNoneExp body := by
        simpa [everyFnVarsNone, fnVarsNoneExp] using annotations
      exact h.1
    · apply Set.disjoint_left.mpr
      intro k ownMember nestedMember
      have ownMember' : k ∈ own := by
        simpa [own, Nat.add_comm] using ownMember
      exact (separate k nestedMember k ownMember') rfl
    · exact nestedNodup
  · constructor
    · intro k member
      exact fresh' k (List.mem_append_left _ (List.mem_append_left _ member))
    · intro i bound
      have member : loc + 2 * i ∈ own := by
        exact List.mem_map.mpr ⟨i, List.mem_range.mpr bound, rfl⟩
      simpa [Nat.add_comm] using fresh' (loc + 2 * i)
        (List.mem_append_left _ (List.mem_append_right _ member))

/-- Source-level coverage of unknown recursive-binding locations covers all
nested function locations. -/
theorem letrec_source_coverage (names : List Basis.Pure.MlString.MlString) (loc : Nat)
    (fns : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (final : State) (allowed : Set Nat)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain final.1 k → k ∈ allowed) :
    groupLocationsCovered fns final allowed := by
  intro k member unknown
  apply coverage k _ unknown
  simp only [codeLocations, codeLocationsExp, codeLocationsFuns_map, List.append_nil, List.mem_append]
  exact Or.inl (Or.inl member)

/-- Retrying an open group cannot add one of its reserved locations: those
locations are initially fresh and disjoint from every nested function. -/
theorem letrec_open_location_unknown (fuel : Nat) (names : List Basis.Pure.MlString.MlString)
    (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (initial final : State) (out : List ClosLang.Exp)
    (run : callsListFuel fuel (fns.map Prod.snd) initial = some (out, final))
    (initialWf : wellFormed initial)
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial)
    (i : Nat) (bound : i < fns.length) : ¬ sptDomain final.1 (2 * i + loc) := by
  let nested := codeLocations (fns.map Prod.snd)
  let own := (List.range fns.length).map (fun j => loc + 2 * j)
  have nodup : (nested ++ own ++ codeLocationsExp body).Nodup := by
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, nested, own] using distinct
  have groupNodup : (nested ++ own).Nodup := (List.nodup_append.mp nodup).1
  have ownMember : 2 * i + loc ∈ own := by
    apply List.mem_map.mpr
    exact ⟨i, List.mem_range.mpr bound, by simp [Nat.add_comm]⟩
  have noSelf : 2 * i + loc ∉ nested := by
    intro member
    exact (List.nodup_append.mp groupNodup).2.2 _ member _ ownMember rfl
  have fresh' : LabelsFresh (nested ++ own ++ codeLocationsExp body) initial := by
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, nested, own] using fresh
  have noOldLabel : 2 * i + loc + 1 ∉ initial.2.map Prod.fst :=
    fresh' _ (List.mem_append_left _ (List.mem_append_right _ ownMember))
  have noOldKnown : ¬ sptDomain initial.1 (2 * i + loc) := by
    intro known
    apply noOldLabel
    have member : 2 * i + loc + 1 ∈ Set.image Nat.succ (sptDomain initial.1) := ⟨_, known, rfl⟩
    rw [← initialWf.1] at member
    exact member
  intro known
  rcases callsListFuel_knownBound fuel (fns.map Prod.snd) initial final out run _ known with old | generated
  · exact noOldKnown old
  · rcases callsListFuel_labelsBound fuel (fns.map Prod.snd) initial final out run _ generated with
        old | ⟨origin, member, eq⟩
    · exact noOldLabel old
    · have : origin = 2 * i + loc := Nat.add_right_cancel eq.symm
      exact noSelf (this ▸ member)

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

/-- The closed recursive-group case from the source annotation, freshness,
coverage and code-inclusion invariants. -/
theorem callsFuel_letrec_closed_source (fuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (body body' : ClosLang.Exp) (initial afterBodies final g : State)
    (bodies : List ClosLang.Exp) (allowed : Set Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (bodyRun : callsListFuel fuel (fns.map Prod.snd) (insertEach loc fns.length initial) = some (bodies, afterBodies))
    (closed : groupClosed fns bodies)
    (continuation : callsFuel fuel body (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies) = some (body', final))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial)
    (growth : stateExtends (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies) g)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain afterBodies.1 k → k ∈ allowed)
    (included : codeIncludes g.2 code) :
    callsFuel (fuel + 1) (.letrec names (some loc) none fns body) initial =
      some (.letrec names (some loc) none (callsList loc fns) body', final) ∧
    recClosureRelFuel fuel g allowed code loc fns (callsList loc fns) := by
  obtain ⟨wf, nestedFresh, ownFresh⟩ := letrec_source_invariants names loc fns body initial
    locations annotations distinct fresh
  exact callsFuel_letrec_closed_invariant fuel names loc fns body body' initial afterBodies final g bodies allowed code
    bodyRun closed continuation wf initialWf nestedFresh ownFresh growth
    (letrec_source_coverage names loc fns body afterBodies allowed coverage)
    (codeIncludes_of_stateExtends _ g code growth included)

/-- The open recursive-group case from the source invariants. Reserved group
locations are shown to remain unknown after the retry. -/
theorem callsFuel_letrec_open_source (fuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (body body' : ClosLang.Exp) (initial afterProbe afterRetry final g : State)
    (probeBodies retryBodies : List ClosLang.Exp) (allowed : Set Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (probe : callsListFuel fuel (fns.map Prod.snd) (insertEach loc fns.length initial) = some (probeBodies, afterProbe))
    (notClosed : ¬groupClosed fns probeBodies)
    (retry : callsListFuel fuel (fns.map Prod.snd) initial = some (retryBodies, afterRetry))
    (continuation : callsFuel fuel body afterRetry = some (body', final))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial)
    (growth : stateExtends afterRetry g)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain afterRetry.1 k → k ∈ allowed)
    (included : codeIncludes g.2 code) :
    callsFuel (fuel + 1) (.letrec names (some loc) none fns body) initial =
      some (.letrec names (some loc) none ((fns.map Prod.fst).zip retryBodies) body', final) ∧
    recClosureRelFuel fuel g allowed code loc fns ((fns.map Prod.fst).zip retryBodies) := by
  obtain ⟨wf, nestedFresh, ownFresh⟩ := letrec_source_invariants names loc fns body initial
    locations annotations distinct fresh
  have ownAllowed : ∀ i, i < fns.length → 2 * i + loc ∈ allowed := by
    intro i bound
    have member : 2 * i + loc ∈ codeLocations [.letrec names (some loc) none fns body] := by
      simp only [codeLocations, codeLocationsExp, codeLocationsFuns_map, List.append_nil, List.mem_append]
      left
      right
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr bound, by simp [Nat.add_comm]⟩
    exact coverage (2 * i + loc) member (letrec_open_location_unknown fuel names loc fns body
      initial afterRetry retryBodies retry initialWf distinct fresh i bound)
  exact callsFuel_letrec_open_invariant fuel names loc fns body body' initial afterProbe afterRetry final g
    probeBodies retryBodies allowed code probe notClosed retry continuation wf initialWf nestedFresh ownFresh growth
    (letrec_source_coverage names loc fns body afterRetry allowed coverage) ownAllowed
    (codeIncludes_of_stateExtends afterRetry g code growth included)

end Flapjack.Compiler.Backend.ClosCall
