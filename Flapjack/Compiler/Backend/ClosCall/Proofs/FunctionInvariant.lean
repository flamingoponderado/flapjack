import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateFunction
import Flapjack.Compiler.Backend.ClosCall.Proofs.KnownOrigins

/-! Connecting function extraction to the direct-call closure invariant. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

/-- The source function's annotation, distinctness, and label-freshness
conditions imply the three corresponding recursive-closure conditions. -/
theorem fn_source_invariants (name : Basis.Pure.MlString.MlString) (loc arity : Nat)
    (body : ClosLang.Exp) (initial : State)
    (locations : everyFnLocationSome [.fn name (some loc) none arity body])
    (annotations : everyFnVarsNone [.fn name (some loc) none arity body])
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.fn name (some loc) none arity body]) initial) :
    recClosureWellFormed loc [(arity, body)] ∧
      (∀ k ∈ codeLocations (([(arity, body)] : List (Nat × ClosLang.Exp)).map Prod.snd),
        k + 1 ∉ initial.2.map Prod.fst) ∧
      (∀ i, i < ([(arity, body)] : List (Nat × ClosLang.Exp)).length →
        2 * i + loc + 1 ∉ initial.2.map Prod.fst) := by
  have nodup : (codeLocationsExp body ++ [loc]).Nodup := by
    simpa [codeLocations, codeLocationsExp] using distinct
  have nestedNodup : (codeLocationsExp body).Nodup := (List.nodup_append.mp nodup).1
  have noSelf : loc ∉ codeLocationsExp body := by
    intro member
    exact (List.nodup_append.mp nodup).2.2 loc member loc (by simp) rfl
  have fresh' : LabelsFresh (codeLocationsExp body ++ [loc]) initial := by
    simpa [codeLocations, codeLocationsExp] using fresh
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [everyFnLocationSome, fnLocationSomeExp] using locations
    · simpa [everyFnVarsNone, fnVarsNoneExp] using annotations
    · simpa [codeLocations_singleton] using noSelf
    · simpa [codeLocations] using nestedNodup
  · constructor
    · intro k member
      apply fresh' k
      simp only [List.map_singleton, codeLocations_singleton] at member
      exact List.mem_append_left _ member
    · intro i bound
      have zero : i = 0 := by simp at bound; omega
      subst i
      simpa using fresh' loc (by simp)

/-- Coverage of all unknown source-function locations includes the nested
function locations required by the recursive-closure relation. -/
theorem fn_source_coverage (name : Basis.Pure.MlString.MlString) (loc arity : Nat)
    (body : ClosLang.Exp) (final : State) (allowed : Set Nat)
    (coverage : ∀ k ∈ codeLocations [.fn name (some loc) none arity body],
      ¬ sptDomain final.1 k → k ∈ allowed) :
    groupLocationsCovered [(arity, body)] final allowed := by
  intro k member unknown
  apply coverage k _ unknown
  simpa [codeLocations, codeLocationsExp] using Or.inl (b := k = loc) member

/-- An open-function retry cannot add its own reserved location: it was not
known initially and, by distinctness, is not a nested closure location. -/
theorem fn_open_location_unknown (fuel : Nat) (name : Basis.Pure.MlString.MlString)
    (loc arity : Nat) (body body' : ClosLang.Exp) (initial final : State)
    (run : callsFuel fuel body initial = some (body', final))
    (initialWf : wellFormed initial)
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.fn name (some loc) none arity body]) initial) :
    ¬ sptDomain final.1 loc := by
  have nodup : (codeLocationsExp body ++ [loc]).Nodup := by
    simpa [codeLocations, codeLocationsExp] using distinct
  have noSelf : loc ∉ codeLocationsExp body := by
    intro member
    exact (List.nodup_append.mp nodup).2.2 loc member loc (by simp) rfl
  have fresh' : LabelsFresh (codeLocationsExp body ++ [loc]) initial := by
    simpa [codeLocations, codeLocationsExp] using fresh
  have noOldLabel : loc + 1 ∉ initial.2.map Prod.fst := fresh' loc (by simp)
  have noOldKnown : ¬ sptDomain initial.1 loc := by
    intro known
    apply noOldLabel
    have member : loc + 1 ∈ Set.image Nat.succ (sptDomain initial.1) := ⟨loc, known, rfl⟩
    rw [← initialWf.1] at member
    exact member
  intro known
  rcases callsFuel_knownBound fuel body initial final body' run loc known with old | generated
  · exact noOldKnown old
  · rcases callsFuel_labelsBound fuel body initial final body' run (loc + 1) generated with old | ⟨origin, member, eq⟩
    · exact noOldLabel old
    · have : origin = loc := Nat.add_right_cancel eq.symm
      exact noSelf (this ▸ member)

/-- A successful closed-function traversal both emits the direct-call stub
and establishes the recursive-closure relation, provided the enclosing pass
invariants supply freshness, state growth, location coverage, and installed
code. Those invariants remain obligations of the enclosing simulation. -/
theorem callsFuel_fn_closed_invariant (fuel : Nat)
    (name : Basis.Pure.MlString.MlString) (loc arity : Nat) (body body' : ClosLang.Exp)
    (initial afterProbe g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (bodyRun : callsFuel fuel body (insertEach loc 1 initial) = some (body', afterProbe))
    (closed : ∀ n, freeVarExp n body' → n < arity)
    (wf : recClosureWellFormed loc [(arity, body)]) (initialWf : wellFormed initial)
    (nestedFresh : ∀ k ∈ codeLocations (([(arity, body)] : List (Nat × ClosLang.Exp)).map Prod.snd),
      k + 1 ∉ initial.2.map Prod.fst)
    (ownFresh : ∀ i, i < ([(arity, body)] : List (Nat × ClosLang.Exp)).length →
      2 * i + loc + 1 ∉ initial.2.map Prod.fst)
    (growth : stateExtends (codeList loc [(arity, body')] afterProbe) g)
    (covered : groupLocationsCovered [(arity, body)] afterProbe allowed)
    (included : codeIncludes (codeList loc [(arity, body')] afterProbe).2 code) :
    callsFuel (fuel + 1) (.fn name (some loc) none arity body) initial =
      some (.fn name (some loc) none arity (.call .none 0 (loc + 1) (ClosCall.variables .none arity)),
        codeList loc [(arity, body')] afterProbe) ∧
    recClosureRelFuel (fuel + 1) g allowed code loc [(arity, body)]
      [(arity, .call .none 0 (loc + 1) (ClosCall.variables .none arity))] := by
  have closedCheck := (closedFuel_fn fuel name (some loc) none arity body').mpr closed
  constructor
  · simp [callsFuel, bodyRun, closedCheck, codeList]
  · refine ⟨initial, wf, initialWf, nestedFresh, ownFresh, [body'], afterProbe, ?_, Or.inl ?_⟩
    · simp [callsListBounded, callsListFuel, bodyRun]
    · refine ⟨?_, ?_, ?_, covered, ?_⟩
      · simpa [groupClosed] using closed
      · exact ⟨.none, 0, by simp [callsListSource, variablesSource_eq_variables]⟩
      · simpa using growth
      · simpa using included

/-- If the probe finds an open function, conversion retries from the original
state and relates the retained closure to that retry's transformed body. -/
theorem callsFuel_fn_open_invariant (fuel : Nat)
    (name : Basis.Pure.MlString.MlString) (loc arity : Nat) (body probeBody body' : ClosLang.Exp)
    (initial afterProbe afterOpen g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (bodyProbe : callsFuel fuel body (insertEach loc 1 initial) = some (probeBody, afterProbe))
    (notClosed : ¬(∀ n, freeVarExp n probeBody → n < arity))
    (retry : callsFuel fuel body initial = some (body', afterOpen))
    (wf : recClosureWellFormed loc [(arity, body)]) (initialWf : wellFormed initial)
    (nestedFresh : ∀ k ∈ codeLocations (([(arity, body)] : List (Nat × ClosLang.Exp)).map Prod.snd),
      k + 1 ∉ initial.2.map Prod.fst)
    (ownFresh : ∀ i, i < ([(arity, body)] : List (Nat × ClosLang.Exp)).length →
      2 * i + loc + 1 ∉ initial.2.map Prod.fst)
    (growth : stateExtends afterOpen g)
    (covered : groupLocationsCovered [(arity, body)] afterOpen allowed)
    (ownAllowed : loc ∈ allowed) (included : codeIncludes afterOpen.2 code) :
    callsFuel (fuel + 1) (.fn name (some loc) none arity body) initial =
      some (.fn name (some loc) none arity body', afterOpen) ∧
    recClosureRelFuel (fuel + 1) g allowed code loc [(arity, body)] [(arity, body')] := by
  obtain ⟨check, closedCheck⟩ := closedFuel_succeeds fuel (.fn name (some loc) none arity probeBody)
  have checkFalse : check = false := by
    cases check with
    | false => rfl
    | true => exact False.elim (notClosed ((closedFuel_fn fuel name (some loc) none arity probeBody).mp closedCheck))
  subst check
  constructor
  · simp [callsFuel, bodyProbe, closedCheck, retry]
  · refine ⟨initial, wf, initialWf, nestedFresh, ownFresh, [probeBody], afterProbe, ?_, Or.inr ?_⟩
    · simp [callsListBounded, callsListFuel, bodyProbe]
    · refine ⟨?_, [body'], afterOpen, ?_, ?_, growth, covered, ?_, included⟩
      · simpa [groupClosed] using notClosed
      · simp [callsListBounded, callsListFuel, retry]
      · rfl
      · intro i bound
        have : i = 0 := by simp at bound; omega
        simpa [this] using ownAllowed

/-- Closed-function invariant from the source theorem's annotation,
distinctness, freshness, and location-coverage conditions. -/
theorem callsFuel_fn_closed_source (fuel : Nat)
    (name : Basis.Pure.MlString.MlString) (loc arity : Nat) (body body' : ClosLang.Exp)
    (initial afterProbe g : State) (allowed : Set Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (bodyRun : callsFuel fuel body (insertEach loc 1 initial) = some (body', afterProbe))
    (closed : ∀ n, freeVarExp n body' → n < arity)
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.fn name (some loc) none arity body])
    (annotations : everyFnVarsNone [.fn name (some loc) none arity body])
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.fn name (some loc) none arity body]) initial)
    (growth : stateExtends (codeList loc [(arity, body')] afterProbe) g)
    (coverage : ∀ k ∈ codeLocations [.fn name (some loc) none arity body],
      ¬ sptDomain afterProbe.1 k → k ∈ allowed)
    (included : codeIncludes (codeList loc [(arity, body')] afterProbe).2 code) :
    callsFuel (fuel + 1) (.fn name (some loc) none arity body) initial =
      some (.fn name (some loc) none arity (.call .none 0 (loc + 1) (ClosCall.variables .none arity)),
        codeList loc [(arity, body')] afterProbe) ∧
    recClosureRelFuel (fuel + 1) g allowed code loc [(arity, body)]
      [(arity, .call .none 0 (loc + 1) (ClosCall.variables .none arity))] := by
  obtain ⟨wf, nestedFresh, ownFresh⟩ := fn_source_invariants name loc arity body initial
    locations annotations distinct fresh
  exact callsFuel_fn_closed_invariant fuel name loc arity body body' initial afterProbe g allowed code
    bodyRun closed wf initialWf nestedFresh ownFresh growth
    (fn_source_coverage name loc arity body afterProbe allowed coverage) included

/-- Open-function invariant from the source conditions. The reserved
location is derived to remain unknown after the retry. -/
theorem callsFuel_fn_open_source (fuel : Nat)
    (name : Basis.Pure.MlString.MlString) (loc arity : Nat) (body probeBody body' : ClosLang.Exp)
    (initial afterProbe afterOpen g : State) (allowed : Set Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (bodyProbe : callsFuel fuel body (insertEach loc 1 initial) = some (probeBody, afterProbe))
    (notClosed : ¬(∀ n, freeVarExp n probeBody → n < arity))
    (retry : callsFuel fuel body initial = some (body', afterOpen))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.fn name (some loc) none arity body])
    (annotations : everyFnVarsNone [.fn name (some loc) none arity body])
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.fn name (some loc) none arity body]) initial)
    (growth : stateExtends afterOpen g)
    (coverage : ∀ k ∈ codeLocations [.fn name (some loc) none arity body],
      ¬ sptDomain afterOpen.1 k → k ∈ allowed)
    (included : codeIncludes afterOpen.2 code) :
    callsFuel (fuel + 1) (.fn name (some loc) none arity body) initial =
      some (.fn name (some loc) none arity body', afterOpen) ∧
    recClosureRelFuel (fuel + 1) g allowed code loc [(arity, body)] [(arity, body')] := by
  obtain ⟨wf, nestedFresh, ownFresh⟩ := fn_source_invariants name loc arity body initial
    locations annotations distinct fresh
  have unknown := fn_open_location_unknown fuel name loc arity body body' initial afterOpen retry
    initialWf distinct fresh
  have ownAllowed : loc ∈ allowed := by
    apply coverage loc _ unknown
    simp [codeLocations, codeLocationsExp]
  exact callsFuel_fn_open_invariant fuel name loc arity body probeBody body' initial afterProbe afterOpen g
    allowed code bodyProbe notClosed retry wf initialWf nestedFresh ownFresh growth
    (fn_source_coverage name loc arity body afterOpen allowed coverage) ownAllowed included

end Flapjack.Compiler.Backend.ClosCall
