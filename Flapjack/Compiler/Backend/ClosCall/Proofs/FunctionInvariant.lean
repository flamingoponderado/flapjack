import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateFunction

/-! Connecting function extraction to the direct-call closure invariant. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

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

end Flapjack.Compiler.Backend.ClosCall
