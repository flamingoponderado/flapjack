import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxCons

/-! Exception-handler case of known-function approximation correctness. -/
namespace Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Handle
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Merge preserves singleton approximation relations from either branch. -/
theorem mergeSingletonLeft (a b : ValApprox) (vs : List ClosSem.Value)
    (h : List.Forall₂ ValApproxVal [a] vs) : List.Forall₂ ValApproxVal [mergeHOL a b] vs := by
  cases h with
  | cons rel tail =>
    cases tail
    exact .cons (valApproxValMerge _ _ _ (Or.inl rel)) .nil

/-- Merge preserves singleton approximation relations from the handler. -/
theorem mergeSingletonRight (a b : ValApprox) (vs : List ClosSem.Value)
    (h : List.Forall₂ ValApproxVal [b] vs) : List.Forall₂ ValApproxVal [mergeHOL a b] vs := by
  cases h with
  | cons rel tail =>
    cases tail
    exact .cons (valApproxValMerge _ _ _ (Or.inr rel)) .nil

/-- Exception-handler case of the original approximation theorem, with the
source body and result-dependent handler induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxHandle {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (handlerIH : ∀ (ea1 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox),
      (ea1, g1) = knownListTotal c [body] aenv g0 → KnownApproxInvariant C F c [handler] (.other :: aenv) g1)
    (bodyIH : KnownApproxInvariant C F c [body] aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.handle trace body handler] aenv g0 = (eas, g) ∧
      evaluate [.handle trace body handler] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.handle trace body handler] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.handle trace body handler] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.handle trace body handler], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  rcases h with ⟨known, run, unique, related, approx, disjoint, oracle, safe, envSafe, exprSafe, approxSafe, globalsSafe⟩
  have uniqueBoth : uniqueSetGlobals ([body] ++ [handler]) s0.compileOracle := by
    simpa [uniqueSetGlobals, elistGlobals, setGlobals, FlatProps.unionGlobalBag,
      FlatProps.emptyGlobalBag, Nat.add_assoc] using unique
  have ⟨bodyUnique, handlerUnique, swappedUnique⟩ := Cons.uniqueParts [body] [handler] s0.compileOracle uniqueBoth
  have ⟨bodyDisjoint, handlerDisjoint⟩ :=
    (mglobalsDisjointRw s0.globals body handler body handler body [] trace .install [] none none [] 0 0).2.2.1.mp disjoint
  have bothSafe := exprSafe (.handle trace body handler) (by simp)
  simp only [esgcFree] at bothSafe
  have bodySafe : ∀ e ∈ [body], esgcFree e := by simpa using bothSafe.1
  have handlerSafe : ∀ e ∈ [handler], esgcFree e := by simpa using bothSafe.2
  cases hk : knownListTotal c [body] aenv g0 with
  | mk ea1 g1 =>
    obtain ⟨e1, a1, eq1⟩ := knownListTotal_single_result c body aenv g0 g1 ea1 hk
    subst ea1
    cases hh : knownListTotal c [handler] (.other :: aenv) g1 with
    | mk ea2 g2 =>
      obtain ⟨e2, a2, eq2⟩ := knownListTotal_single_result c handler (.other :: aenv) g1 g2 ea2 hh
      subst ea2
      rw [knownListTotal_handle, hk] at known
      dsimp only at known
      rw [hh] at known
      simp [knownSourceHead] at known
      rcases known with ⟨rfl, rfl⟩
      rw [evaluate, fixClock_evaluate] at run
      cases hr : evaluate [body] (env ++ extra) s0 with
      | mk bodyResult middle =>
        have bodyResultApprox := bodyIH [(e1, a1)] g1 env extra s0 bodyResult middle
          ⟨hk, hr, bodyUnique, related, approx, bodyDisjoint, oracle, safe, envSafe, bodySafe, approxSafe, globalsSafe⟩
        have finalIfSkipped : stateGlobalsApprox middle g2 :=
          ApproxEvaluate.stateGlobalsApproxKnownListEvaluate [body] (env ++ extra) s0 bodyResult middle
            c [handler] (.other :: aenv) g1 [(e2, a2)] g2
            ⟨hr, hh, safe, envSafe, bodySafe, handlerDisjoint, uniqueBoth, bodyResultApprox.1⟩
        rw [hr] at run
        cases bodyResult with
        | val values =>
          cases run
          refine ⟨finalIfSkipped, ?_⟩
          intro vs eq
          cases eq
          simpa using mergeSingletonLeft a1 a2 values (by simpa using bodyResultApprox.2 values rfl)
        | err error =>
          cases error with
          | abort reason =>
            cases run
            exact ⟨finalIfSkipped, by intro vs impossible; cases impossible⟩
          | raise value =>
            have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals [body] (env ++ extra) s0
              (.err (.raise value)) middle ⟨hr, safe, bodySafe, envSafe⟩
            have valueSafe : vsgcFree value := by simpa [rsgcFree] using safety.2.1
            have nextUnique := uniqueSetGlobalsEvaluate [body] [handler] (env ++ extra) s0 middle
              (.err (.raise value)) ⟨handlerUnique, hr⟩
            have nextDisjoint := mglobalsDisjointEvaluate s0 [handler] [body] (env ++ extra)
              (.err (.raise value)) middle ⟨hr, safe, envSafe, bodySafe, swappedUnique, handlerDisjoint⟩
            have nextOracle := oracleGapproxDisjointLemma [body] (env ++ extra) s0 (.err (.raise value)) middle
              c aenv g0 [(e1, a1)] g1 ⟨hr, hk, bodyUnique, oracle⟩
            have nextGlobalsSafe := (PreserveSafety.knownPreservesEsgcFree c [body] aenv g0
              [(e1, a1)] g1 ⟨hk, bodySafe, approxSafe, globalsSafe⟩).2.2
            have extendedSafe : ∀ v ∈ (value :: env) ++ extra, vsgcFree v := by
              intro v member
              rcases List.mem_cons.mp member with same | rest
              · subst v; exact valueSafe
              · exact envSafe v rest
            have extendedApproxSafe : ∀ a ∈ ValApprox.other :: aenv, valApproxSgcFree a := by
              intro a member
              rcases List.mem_cons.mp member with same | rest
              · subst a; simp [valApproxSgcFree]
              · exact approxSafe a rest
            cases ht : evaluate [handler] ((value :: env) ++ extra) middle with
            | mk handlerResult last =>
              have handlerResultApprox := handlerIH [(e1, a1)] g1 hk.symm [(e2, a2)] g2
                (value :: env) extra middle handlerResult last
                ⟨hh, ht, nextUnique, .cons (.other value) related, bodyResultApprox.1, nextDisjoint,
                  nextOracle, safety.1, extendedSafe, handlerSafe, extendedApproxSafe, nextGlobalsSafe⟩
              change evaluate [handler] ((value :: env) ++ extra) middle = (res, s) at run
              rw [ht] at run
              cases handlerResult with
              | err error =>
                cases run
                exact ⟨handlerResultApprox.1, by intro vs impossible; cases impossible⟩
              | val values =>
                cases run
                refine ⟨handlerResultApprox.1, ?_⟩
                intro vs eq
                cases eq
                simpa using mergeSingletonRight a1 a2 values (by simpa using handlerResultApprox.2 values rfl)

end Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Handle
