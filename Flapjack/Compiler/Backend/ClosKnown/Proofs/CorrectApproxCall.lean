module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxCons
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxRuntime

@[expose] public section


/-! Direct-call case of known-function approximation correctness. -/
namespace Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Call
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness


/-- A successful code lookup in a safe state returns safe code and the same
arguments. This is Flapjack proof infrastructure. -/
private theorem findCodeSafe {C F : Type} (location : Nat) (args selected : List ClosSem.Value)
    (body : ClosLang.Exp) (state : State C F) (safe : ssgcFree state)
    (found : findCode location args state.code = some (selected, body)) :
    selected = args ∧ setGlobals body = FlatProps.emptyGlobalBag := by
  change (state.code.lookup location).bind
    (fun entry => if args.length = entry.1 then some (args, entry.2) else none) = some (selected, body) at found
  simp only [Option.bind_eq_some_iff] at found
  rcases found with ⟨⟨arity, codeBody⟩, lookup, found⟩
  split at found <;> simp_all
  exact safe.1 _ _ _ lookup

/-- Direct-call case of the original approximation theorem, with the source
argument-list induction hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxCall {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (ticks dest : Nat) (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.call trace ticks dest xs] aenv g0 = (eas, g) ∧
      evaluate [.call trace ticks dest xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.call trace ticks dest xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.call trace ticks dest xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.call trace ticks dest xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  rcases h with ⟨known, run, unique, related, approx, disjoint, oracle, safe, envSafe, exprSafe, approxSafe, globalsSafe⟩
  have callRun := run
  have argsUnique : uniqueSetGlobals xs s0.compileOracle := by
    simpa [uniqueSetGlobals, elistGlobals_append, elistGlobals, setGlobals,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using unique
  have argsDisjoint : mglobalsDisjoint s0.globals xs := by
    simpa [mglobalsDisjoint, elistGlobals, setGlobals,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using disjoint
  have argsSafe : ∀ e ∈ xs, esgcFree e := by
    have h := exprSafe (.call trace ticks dest xs) (by simp)
    simpa [esgcFree, esgcFreeList_iff] using h
  cases hk : knownListTotal c xs aenv g0 with
  | mk ea g1 =>
    rw [knownListTotal_call, hk] at known
    simp at known
    rcases known with ⟨rfl, rfl⟩
    have resultRel : ∀ vs, res = .val vs → List.Forall₂ ValApproxVal [.other] vs := by
      intro vs eq
      have valueRun : evaluate [.call trace ticks dest xs] (env ++ extra) s0 = (.val vs, s) := by
        simpa [eq] using callRun
      obtain ⟨v, rfl⟩ := evaluate_singleton_value (.call trace ticks dest xs) (env ++ extra) s0 s vs valueRun
      exact .cons (.other v) .nil
    rw [evaluate, fixClock_evaluate] at run
    cases hr : evaluate xs (env ++ extra) s0 with
    | mk argResult middle =>
      have argApprox := argsIH ea g1 env extra s0 argResult middle
        ⟨hk, hr, argsUnique, related, approx, argsDisjoint, oracle, safe, envSafe, argsSafe, approxSafe, globalsSafe⟩
      rw [hr] at run
      cases argResult with
      | err error =>
        cases run
        exact ⟨argApprox.1, resultRel⟩
      | val values =>
        have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals xs (env ++ extra) s0
          (.val values) middle ⟨hr, safe, argsSafe, envSafe⟩
        have valuesSafe : ∀ v ∈ values, vsgcFree v := by simpa [rsgcFree] using safety.2.1
        have middleOracle := oracleGapproxDisjointLemma xs (env ++ extra) s0 (.val values) middle
          c aenv g0 ea g1 ⟨hr, hk, argsUnique, oracle⟩
        dsimp only at run
        cases codeRun : findCode dest values middle.code with
        | none =>
          simp [codeRun] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨argApprox.1, resultRel⟩
        | some entry =>
          obtain ⟨callArgs, body⟩ := entry
          have ⟨sameArgs, bodyEmpty⟩ := findCodeSafe dest values callArgs body middle safety.1 codeRun
          have callArgsSafe : ∀ v ∈ callArgs, vsgcFree v := by simpa [sameArgs] using valuesSafe
          have bodySafe : ∀ e ∈ [body], esgcFree e := by simpa using setGlobalsEmptyEsgcFree body bodyEmpty
          by_cases timeout : middle.clock < ticks + 1
          · simp [codeRun, timeout] at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨by simpa [stateGlobalsApprox] using argApprox.1, resultRel⟩
          · have bodyRun : evaluate [body] callArgs (decClock (ticks + 1) middle) = (res, s) := by
              simpa [codeRun, timeout] using run
            have emptyBag : elistGlobals [body] = FlatProps.emptyGlobalBag := by
              funext i
              simp [elistGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, bodyEmpty, Flapjack.bagUnion, Flapjack.emptyBag]
            have finalApprox := ApproxRuntime.stateGlobalsApproxEvaluateEmpty [body] callArgs
              (decClock (ticks + 1) middle) res s g1 bodyRun
              ((ssgcFreeDecClock (ticks + 1) middle).2 safety.1) callArgsSafe bodySafe emptyBag
              (by simpa [decClock] using middleOracle)
              (by simpa [decClock, stateGlobalsApprox] using argApprox.1)
            exact ⟨finalApprox, resultRel⟩

end Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Call
