module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.FunctionInvariant

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section

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

/-- A successful traversal cannot introduce an unknown location absent from
the traversed expression, when the initial pass state is well formed. -/
theorem callsFuel_unknown_preserved (fuel : Nat) (body out : ClosLang.Exp)
    (initial final : State) (run : callsFuel fuel body initial = some (out, final))
    (well : weaklyWellFormed initial) (key : Nat) (outside : key ∉ codeLocationsExp body)
    (unknown : ¬ sptDomain initial.1 key) : ¬ sptDomain final.1 key := by
  have noOldLabel : key + 1 ∉ initial.2.map Prod.fst := by
    intro member
    have imageMember : key + 1 ∈ Set.image Nat.succ (sptDomain initial.1) := well member
    obtain ⟨other, known, equal⟩ := imageMember
    have : other = key := Nat.succ.inj equal
    exact unknown (this ▸ known)
  intro known
  rcases callsFuel_knownBound fuel body initial final out run key known with old | generated
  · exact unknown old
  · rcases callsFuel_labelsBound fuel body initial final out run (key + 1) generated with
        old | ⟨origin, member, equal⟩
    · exact noOldLabel old
    · have : origin = key := Nat.add_right_cancel equal.symm
      exact outside (this ▸ member)

/-- A successful single-expression traversal extends its pass state when
its closure locations are distinct and fresh. -/
theorem callsFuel_stateExtends (fuel : Nat) (body out : ClosLang.Exp)
    (initial final : State) (run : callsFuel fuel body initial = some (out, final))
    (distinct : (codeLocationsExp body).Nodup) (fresh : LabelsFresh (codeLocationsExp body) initial)
    (oldDistinct : (initial.2.map Prod.fst).Nodup) : stateExtends initial final := by
  have listRun : callsListBounded (fuel + 1) [body] initial = some ([out], final) := by
    simp [callsListBounded, callsListFuel, run]
  exact callsListBounded_stateExtends (fuel + 1) [body] initial final [out] listRun
    (by simpa [codeLocations] using distinct) (by simpa [codeLocations] using fresh) oldDistinct

/-- Labels belonging to the continuation remain fresh after retrying the
recursive function bodies, since the two location lists are disjoint. -/
theorem letrec_continuation_fresh_after_retry (fuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat)
    (fns : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (initial afterRetry : State) (retryBodies : List ClosLang.Exp)
    (retry : callsListFuel fuel (fns.map Prod.snd) initial = some (retryBodies, afterRetry))
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial) :
    (codeLocationsExp body).Nodup ∧ LabelsFresh (codeLocationsExp body) afterRetry := by
  let nested := codeLocations (fns.map Prod.snd)
  let own := (List.range fns.length).map (fun i => loc + 2 * i)
  have nodup : (nested ++ own ++ codeLocationsExp body).Nodup := by
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, nested, own] using distinct
  have fresh' : LabelsFresh (nested ++ own ++ codeLocationsExp body) initial := by
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, nested, own] using fresh
  refine ⟨(List.nodup_append.mp nodup).2.1, ?_⟩
  intro key member generated
  have noOld := fresh' key (List.mem_append_right _ member)
  rcases callsListFuel_labelsBound fuel (fns.map Prod.snd) initial afterRetry retryBodies retry
      (key + 1) generated with old | ⟨origin, originMember, equal⟩
  · exact noOld old
  · have originEq : origin = key := Nat.add_right_cancel equal.symm
    subst origin
    exact (List.nodup_append.mp nodup).2.2 key (List.mem_append_left _ originMember) key member rfl

/-- In the extracted branch, the continuation's labels are fresh after both
the group traversal and installation of its generated auxiliary code. -/
theorem letrec_continuation_fresh_after_extraction (fuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat)
    (fns : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (initial afterBodies : State) (bodies : List ClosLang.Exp)
    (bodyRun : callsListFuel fuel (fns.map Prod.snd) (insertEach loc fns.length initial) =
      some (bodies, afterBodies))
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial) :
    (codeLocationsExp body).Nodup ∧
      LabelsFresh (codeLocationsExp body) (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies) := by
  let nested := codeLocations (fns.map Prod.snd)
  let own := (List.range fns.length).map (fun i => loc + 2 * i)
  have nodup : (nested ++ own ++ codeLocationsExp body).Nodup := by
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, nested, own] using distinct
  have fresh' : LabelsFresh (nested ++ own ++ codeLocationsExp body) initial := by
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, nested, own] using fresh
  refine ⟨(List.nodup_append.mp nodup).2.1, ?_⟩
  intro key member generated
  have noOld := fresh' key (List.mem_append_right _ member)
  have separate := (List.nodup_append.mp nodup).2.2
  rw [codeList_labels] at generated
  simp only [List.mem_append, List.mem_reverse, List.mem_map, List.mem_range] at generated
  rcases generated with ⟨i, bound, equal⟩ | existing
  · have size := convertedFunctions_length fuel fns (insertEach loc fns.length initial) afterBodies bodies bodyRun
    rw [size] at bound
    have ownMember : loc + 2 * i ∈ nested ++ own := by
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr bound, rfl⟩
    have keyEq : loc + 2 * i = key := by omega
    exact (separate _ ownMember key member) keyEq
  · have existing' : key + 1 ∈ afterBodies.2.map Prod.fst := List.mem_map.mpr existing
    rcases callsListFuel_labelsBound fuel (fns.map Prod.snd) (insertEach loc fns.length initial)
      afterBodies bodies bodyRun (key + 1) existing' with old | ⟨origin, originMember, equal⟩
    · apply noOld
      simpa [insertEach] using old
    · have originEq : origin = key := Nat.add_right_cancel equal.symm
      subst origin
      exact separate key (List.mem_append_left _ originMember) key member rfl

/-- Installing the extracted group restores full compiler-state
well-formedness after its speculative traversal. Label distinctness is supplied
separately by the enclosing traversal. This is Flapjack-specific induction
infrastructure. -/
theorem letrec_extracted_state_wellFormed (fuel loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (initial afterBodies : State) (bodies : List ClosLang.Exp)
    (run : callsListFuel fuel (fns.map Prod.snd) (insertEach loc fns.length initial) = some (bodies, afterBodies))
    (initialWf : wellFormed initial)
    (distinct : ((codeList loc ((fns.map Prod.fst).zip bodies) afterBodies).2.map Prod.fst).Nodup) :
    wellFormed (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies) := by
  have size := convertedFunctions_length fuel fns (insertEach loc fns.length initial) afterBodies bodies run
  have weak : weaklyWellFormed (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies) := by
    apply weaklyWellFormed_codeList
    · exact callsListFuel_weaklyWellFormed fuel (fns.map Prod.snd) _ afterBodies bodies run
        (weaklyWellFormed_insertEach loc fns.length initial (wellFormed_weak initial initialWf))
    · intro key member
      simp only [Set.mem_ofPred_eq, List.mem_map, List.mem_range] at member
      obtain ⟨i, bound, rfl⟩ := member
      simp only [size] at bound
      apply callsListFuel_knownExt fuel _ _ afterBodies bodies run
      exact (insertEach_domain loc fns.length initial _).mpr (Or.inr ⟨i, bound, rfl⟩)
  refine ⟨Set.Subset.antisymm weak ?_, distinct⟩
  intro label member
  obtain ⟨key, known, eq⟩ := member
  have known' : sptDomain afterBodies.1 key := by
    change sptDomain (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies).1 key at known
    rw [codeList_eq_source, codeListSource_fst] at known
    exact known
  rcases callsListFuel_knownBound fuel (fns.map Prod.snd) _ afterBodies bodies run key known' with old | generated
  · rcases (insertEach_domain loc fns.length initial key).mp old with original | ⟨i, bound, keyEq⟩
    · have oldLabel : key + 1 ∈ initial.2.map Prod.fst := by
        have inImage : key + 1 ∈ Set.image Nat.succ (sptDomain initial.1) := ⟨key, original, by omega⟩
        rw [← initialWf.1] at inImage
        exact inImage
      have suffix := callsListFuel_suffix fuel (fns.map Prod.snd) (insertEach loc fns.length initial) afterBodies bodies run
      obtain ⟨front, suffixEq⟩ := suffix
      have later : key + 1 ∈ afterBodies.2.map Prod.fst := by
        rw [← suffixEq, List.map_append]
        exact List.mem_append_right _ (by simpa [insertEach] using oldLabel)
      have : key + 1 ∈ (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies).2.map Prod.fst := by
        rw [codeList_labels]
        exact List.mem_append_right _ later
      simpa [← eq] using this
    · have inCode : key + 1 ∈ (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies).2.map Prod.fst := by
        rw [codeList_labels]
        apply List.mem_append_left
        apply List.mem_reverse.mpr
        apply List.mem_map.mpr
        refine ⟨i, List.mem_range.mpr ?_, ?_⟩
        · simp [size, bound]
        · omega
      simpa [← eq] using inCode
  · have inCode : key + 1 ∈ (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies).2.map Prod.fst := by
      rw [codeList_labels]
      exact List.mem_append_right _ generated
    simpa [← eq] using inCode

/-- A continuation cannot turn an unknown recursive-group location into a
known location. Thus coverage stated at the final pass state also covers
unknown group locations at the intermediate state. -/
theorem letrec_group_coverage_before_continuation (fuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat)
    (fns : List (Nat × ClosLang.Exp)) (body body' : ClosLang.Exp)
    (middle final : State) (allowed : Set Nat)
    (run : callsFuel fuel body middle = some (body', final)) (middleWf : weaklyWellFormed middle)
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain final.1 k → k ∈ allowed) :
    groupLocationsCovered fns middle allowed ∧
      (∀ i, i < fns.length → ¬ sptDomain middle.1 (2 * i + loc) → 2 * i + loc ∈ allowed) := by
  let group := codeLocations (fns.map Prod.snd) ++ (List.range fns.length).map (fun i => loc + 2 * i)
  have nodup : (group ++ codeLocationsExp body).Nodup := by
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, group] using distinct
  have groupCoverage : ∀ k ∈ group, ¬ sptDomain middle.1 k → k ∈ allowed := by
    intro k member unknown
    have outside : k ∉ codeLocationsExp body := by
      intro inBody
      exact (List.nodup_append.mp nodup).2.2 k member k inBody rfl
    have sourceMember : k ∈ codeLocations [.letrec names (some loc) none fns body] := by
      simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, group] using
        List.mem_append_left (codeLocationsExp body) member
    exact coverage k sourceMember (callsFuel_unknown_preserved fuel body body' middle final run middleWf k outside unknown)
  constructor
  · intro k member unknown
    exact groupCoverage k (List.mem_append_left _ member) unknown
  · intro i bound unknown
    apply groupCoverage (2 * i + loc) _ unknown
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr bound, by simp [Nat.add_comm]⟩

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

/-- The closed-group invariant follows from coverage at the final pass state. -/
theorem callsFuel_letrec_closed_final (fuel : Nat)
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
    (growth : stateExtends final g)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain final.1 k → k ∈ allowed)
    (included : codeIncludes g.2 code) :
    callsFuel (fuel + 1) (.letrec names (some loc) none fns body) initial =
      some (.letrec names (some loc) none (callsList loc fns) body', final) ∧
    recClosureRelFuel fuel g allowed code loc fns (callsList loc fns) := by
  obtain ⟨wf, nestedFresh, ownFresh⟩ := letrec_source_invariants names loc fns body initial
    locations annotations distinct fresh
  have middleWf : weaklyWellFormed (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies) := by
    apply weaklyWellFormed_codeList
    · exact callsListFuel_weaklyWellFormed fuel (fns.map Prod.snd) _ afterBodies bodies bodyRun
        (weaklyWellFormed_insertEach loc fns.length initial (wellFormed_weak initial initialWf))
    · intro key member
      simp only [Set.mem_ofPred_eq, List.mem_map, List.mem_range] at member
      obtain ⟨i, bound, rfl⟩ := member
      have size := convertedFunctions_length fuel fns (insertEach loc fns.length initial) afterBodies bodies bodyRun
      rw [size] at bound
      apply callsListFuel_knownExt fuel _ _ afterBodies bodies bodyRun
      exact (insertEach_domain loc fns.length initial _).mpr (Or.inr ⟨i, bound, rfl⟩)
  have wholeRun := callsFuel_letrec_closedBranch fuel names (some loc) none fns body initial afterBodies final
    bodies body' bodyRun closed continuation
  have finalDistinct : (final.2.map Prod.fst).Nodup :=
    callsFuel_labelsDistinct (fuel + 1) (.letrec names (some loc) none fns body) initial final
      (.letrec names (some loc) none (callsList loc fns) body') wholeRun
      (by simpa [codeLocations] using distinct) (by simpa [codeLocations] using fresh) initialWf.2
  have middleDistinct : ((codeList loc ((fns.map Prod.fst).zip bodies) afterBodies).2.map Prod.fst).Nodup :=
    ((callsFuel_suffix fuel body (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies) final
      body' continuation).map Prod.fst).nodup finalDistinct
  obtain ⟨bodyDistinct, bodyFresh⟩ := letrec_continuation_fresh_after_extraction fuel names loc fns body
    initial afterBodies bodies bodyRun distinct fresh
  have middleGrowth : stateExtends (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies) final :=
    callsFuel_stateExtends fuel body body' _ final continuation bodyDistinct bodyFresh middleDistinct
  have groupGrowth := stateExtends_trans _ final g middleGrowth growth
  have covered := (letrec_group_coverage_before_continuation fuel names loc fns body body'
    (codeList loc ((fns.map Prod.fst).zip bodies) afterBodies) final allowed continuation middleWf distinct coverage).1
  have covered' : groupLocationsCovered fns afterBodies allowed := by simpa [codeList, groupLocationsCovered] using covered
  exact callsFuel_letrec_closed_invariant fuel names loc fns body body' initial afterBodies final g bodies allowed code
    bodyRun closed continuation wf initialWf nestedFresh ownFresh groupGrowth covered'
    (codeIncludes_of_stateExtends _ g code groupGrowth included)

/-- The open-group invariant follows from coverage at the final pass state. -/
theorem callsFuel_letrec_open_final (fuel : Nat)
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
    (growth : stateExtends final g)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain final.1 k → k ∈ allowed)
    (included : codeIncludes g.2 code) :
    callsFuel (fuel + 1) (.letrec names (some loc) none fns body) initial =
      some (.letrec names (some loc) none ((fns.map Prod.fst).zip retryBodies) body', final) ∧
    recClosureRelFuel fuel g allowed code loc fns ((fns.map Prod.fst).zip retryBodies) := by
  obtain ⟨wf, nestedFresh, ownFresh⟩ := letrec_source_invariants names loc fns body initial
    locations annotations distinct fresh
  have middleWf : wellFormed afterRetry :=
    callsListFuel_wellFormed fuel (fns.map Prod.snd) initial afterRetry retryBodies retry
      wf.2.2.2 nestedFresh initialWf
  obtain ⟨bodyDistinct, bodyFresh⟩ := letrec_continuation_fresh_after_retry fuel names loc fns body
    initial afterRetry retryBodies retry distinct fresh
  have middleGrowth : stateExtends afterRetry final :=
    callsFuel_stateExtends fuel body body' afterRetry final continuation bodyDistinct bodyFresh middleWf.2
  have groupGrowth := stateExtends_trans afterRetry final g middleGrowth growth
  obtain ⟨covered, ownCovered⟩ := letrec_group_coverage_before_continuation fuel names loc fns body body'
    afterRetry final allowed continuation (wellFormed_weak afterRetry middleWf) distinct coverage
  have ownAllowed : ∀ i, i < fns.length → 2 * i + loc ∈ allowed := by
    intro i bound
    exact ownCovered i bound (letrec_open_location_unknown fuel names loc fns body initial afterRetry
      retryBodies retry initialWf distinct fresh i bound)
  exact callsFuel_letrec_open_invariant fuel names loc fns body body' initial afterProbe afterRetry final g
    probeBodies retryBodies allowed code probe notClosed retry continuation wf initialWf nestedFresh ownFresh groupGrowth
    covered ownAllowed (codeIncludes_of_stateExtends afterRetry g code groupGrowth included)

/-- A successful recursive-binding traversal establishes the group relation
and exposes its continuation traversal, without assuming which pass branch
was selected. -/
theorem callsFuel_letrec_relation (fuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (body out : ClosLang.Exp) (initial final g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (run : callsFuel (fuel + 1) (.letrec names (some loc) none fns body) initial = some (out, final))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial)
    (growth : stateExtends final g)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain final.1 k → k ∈ allowed)
    (included : codeIncludes g.2 code) :
    ∃ targetFns targetBody middle,
      out = .letrec names (some loc) none targetFns targetBody ∧
      callsFuel fuel body middle = some (targetBody, final) ∧
      recClosureRelFuel fuel g allowed code loc fns targetFns := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
  obtain ⟨⟨probeBodies, afterProbe⟩, probe, check, checkRun, rest⟩ := run
  have length : fns.length = probeBodies.length := by
    have h := callsListFuel_length fuel (fns.map Prod.snd) (insertEach loc fns.length initial) afterProbe probeBodies probe
    simpa using h.symm
  have groupCheck : groupClosedFuel fuel fns probeBodies = some check := by
    simpa [groupClosedFuel] using checkRun
  cases check with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff,
      Option.some.injEq, Prod.mk.injEq] at rest
    obtain ⟨⟨retryBodies, afterRetry⟩, retry, ⟨targetBody, final'⟩, continuation, rfl, rfl⟩ := rest
    have notClosed : ¬groupClosed fns probeBodies := (groupClosedFuel_false_iff fuel fns probeBodies length).mp groupCheck
    exact ⟨(fns.map Prod.fst).zip retryBodies, targetBody, afterRetry, rfl, continuation,
      (callsFuel_letrec_open_final fuel names loc fns body targetBody initial afterProbe afterRetry final' g
        probeBodies retryBodies allowed code probe notClosed retry continuation initialWf locations annotations
        distinct fresh growth coverage included).2⟩
  | true =>
    simp only [↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
    obtain ⟨⟨targetBody, final'⟩, continuation, rfl, rfl⟩ := rest
    have closed : groupClosed fns probeBodies := (groupClosedFuel_iff fuel fns probeBodies length).mp groupCheck
    exact ⟨callsList loc fns, targetBody, codeList loc ((fns.map Prod.fst).zip probeBodies) afterProbe,
      rfl, continuation,
      (callsFuel_letrec_closed_final fuel names loc fns body targetBody initial afterProbe final' g probeBodies
        allowed code probe closed continuation initialWf locations annotations distinct fresh growth coverage included).2⟩

/-- The actual recursive-binding continuation starts in a fully well-formed
state with fresh, distinct body locations. This is Flapjack-specific induction
infrastructure. -/
theorem callsFuel_letrec_continuation_wellFormed (fuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (body out : ClosLang.Exp) (initial final : State)
    (run : callsFuel (fuel + 1) (.letrec names (some loc) none fns body) initial = some (out, final))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial) :
    ∃ targetFns targetBody middle,
      out = .letrec names (some loc) none targetFns targetBody ∧
      callsFuel fuel body middle = some (targetBody, final) ∧ wellFormed middle ∧
      (codeLocationsExp body).Nodup ∧ LabelsFresh (codeLocationsExp body) middle := by
  have finalDistinct : (final.2.map Prod.fst).Nodup :=
    callsFuel_labelsDistinct (fuel + 1) (.letrec names (some loc) none fns body) initial final out run
      (by simpa [codeLocations] using distinct) (by simpa [codeLocations] using fresh) initialWf.2
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
  obtain ⟨⟨probeBodies, afterProbe⟩, probe, check, _, rest⟩ := run
  cases check with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
    obtain ⟨⟨retryBodies, afterRetry⟩, retry, ⟨targetBody, final'⟩, continuation, rfl, rfl⟩ := rest
    obtain ⟨wf, nestedFresh, _⟩ := letrec_source_invariants names loc fns body initial locations annotations distinct fresh
    have middleWf := callsListFuel_wellFormed fuel (fns.map Prod.snd) initial afterRetry retryBodies retry
      wf.2.2.2 nestedFresh initialWf
    obtain ⟨bodyDistinct, bodyFresh⟩ := letrec_continuation_fresh_after_retry fuel names loc fns body initial afterRetry retryBodies retry distinct fresh
    exact ⟨_, targetBody, afterRetry, rfl, continuation, middleWf, bodyDistinct, bodyFresh⟩
  | true =>
    simp only [↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
    obtain ⟨⟨targetBody, final'⟩, continuation, rfl, rfl⟩ := rest
    have middleDistinct : ((codeList loc ((fns.map Prod.fst).zip probeBodies) afterProbe).2.map Prod.fst).Nodup :=
      ((callsFuel_suffix fuel body (codeList loc ((fns.map Prod.fst).zip probeBodies) afterProbe) final'
        targetBody continuation).map Prod.fst).nodup finalDistinct
    have middleWf := letrec_extracted_state_wellFormed fuel loc fns initial afterProbe probeBodies probe initialWf middleDistinct
    obtain ⟨bodyDistinct, bodyFresh⟩ := letrec_continuation_fresh_after_extraction fuel names loc fns body initial afterProbe probeBodies probe distinct fresh
    exact ⟨_, targetBody, _, rfl, continuation, middleWf, bodyDistinct, bodyFresh⟩

/-- The transformed recursive group is related at any relation fuel, not
only at the traversal fuel used to produce it. This is Flapjack-specific
adapter infrastructure; it is not a port of a HOL theorem. -/
theorem callsFuel_letrec_relation_atFuel (fuel relationFuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (body out : ClosLang.Exp) (initial final g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (run : callsFuel (fuel + 1) (.letrec names (some loc) none fns body) initial = some (out, final))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial)
    (growth : stateExtends final g)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain final.1 k → k ∈ allowed)
    (included : codeIncludes g.2 code) :
    ∃ targetFns targetBody middle,
      out = .letrec names (some loc) none targetFns targetBody ∧
      callsFuel fuel body middle = some (targetBody, final) ∧
      recClosureRelFuel relationFuel g allowed code loc fns targetFns := by
  obtain ⟨targetFns, targetBody, middle, output, bodyRun, closure⟩ :=
    callsFuel_letrec_relation fuel names loc fns body out initial final g allowed code run initialWf
      locations annotations distinct fresh growth coverage included
  exact ⟨targetFns, targetBody, middle, output, bodyRun,
    (recClosureRelFuel_independent fuel relationFuel g allowed code loc fns targetFns).mp closure⟩

/-- Source-driven recursive-binding evaluation after the actual pass run.
The body hypothesis is the local fuel-aware induction interface; the full
HOL simulation's oracle and growing-state conclusions remain open. -/
theorem callsFuel_letrec_evaluate {C F : Type} (fuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (body out : ClosLang.Exp) (initial final g : State) (allowed : Set Nat)
    (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value) (sourceFinal : ClosSem.State (NumSet × C) F)
    (sourceRun : evaluate [.letrec names (some loc) none fns body] sourceEnv source = (sourceResult, sourceFinal))
    (notType : sourceResult ≠ .err (.abort .typeError))
    (run : callsFuel (fuel + 1) (.letrec names (some loc) none fns body) initial = some (out, final))
    (bodyIH : ∀ targetBody middle, callsFuel fuel body middle = some (targetBody, final) →
      ExprSimFuel (C := C) (F := F) fuel g allowed body targetBody)
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial)
    (growth : stateExtends final g)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain final.1 k → k ∈ allowed)
    (included : codeIncludes g.2 target.code)
    (envs : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (states : StateRelFuel fuel g allowed source target) :
    ∃ targetResult targetFinal,
      evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, target.code.lookup key = some value → targetFinal.code.lookup key = some value) := by
  obtain ⟨targetFns, targetBody, middle, rfl, bodyRun, closure⟩ :=
    callsFuel_letrec_relation fuel names loc fns body out initial final g allowed target.code run initialWf
      locations annotations distinct fresh growth coverage included
  exact evaluate_letrec_fuel fuel g allowed names loc fns targetFns body targetBody (bodyIH targetBody middle bodyRun)
    sourceEnv targetEnv source target sourceResult sourceFinal sourceRun notType envs states closure

end Flapjack.Compiler.Backend.ClosCall
