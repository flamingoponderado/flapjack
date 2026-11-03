import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxCons

/-! Let-binding case of known-function approximation correctness. -/
namespace Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Let
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Let-binding case of the original approximation theorem, with the source
binding and result-dependent body induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxLet {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (xs : List ClosLang.Exp) (body : ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (bodyIH : ∀ (ea1 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox),
      (ea1, g1) = knownListTotal c xs aenv g0 →
      KnownApproxInvariant C F c [body] (ea1.map Prod.snd ++ aenv) g1)
    (bindingsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.let trace xs body] aenv g0 = (eas, g) ∧
      evaluate [.let trace xs body] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.let trace xs body] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.let trace xs body] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.let trace xs body], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  rcases h with ⟨known, run, unique, related, approx, disjoint, oracle, safe, envSafe, exprSafe, approxSafe, globalsSafe⟩
  have uniqueBoth : uniqueSetGlobals (xs ++ [body]) s0.compileOracle := by
    intro n i
    have bound := unique n i
    simp only [elistGlobals_append, elistGlobals, setGlobals,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Nat.add_zero] at bound ⊢
    omega
  have ⟨argsUnique, bodyUnique, swappedUnique⟩ := Cons.uniqueParts xs [body] s0.compileOracle uniqueBoth
  have ⟨argsDisjoint, bodyDisjoint⟩ :=
    (mglobalsDisjointRw s0.globals body body body body body xs trace .install [] none none [] 0 0).2.1.mp disjoint
  have letSafe := exprSafe (.let trace xs body) (by simp)
  simp only [esgcFree, esgcFreeList_iff] at letSafe
  have argsSafe := letSafe.1
  have bodySafe : ∀ e ∈ [body], esgcFree e := by simpa using letSafe.2
  cases hk : knownListTotal c xs aenv g0 with
  | mk ea1 g1 =>
    cases hb : knownListTotal c [body] (ea1.map Prod.snd ++ aenv) g1 with
    | mk ea2 g2 =>
      obtain ⟨bodyExpr, bodyApprox, eq⟩ :=
        knownListTotal_single_result c body (ea1.map Prod.snd ++ aenv) g1 g2 ea2 hb
      subst ea2
      rw [knownListTotal_let, hk] at known
      dsimp only at known
      rw [hb] at known
      simp [knownSourceHead] at known
      rcases known with ⟨rfl, rfl⟩
      rw [evaluate, fixClock_evaluate] at run
      cases hr : evaluate xs (env ++ extra) s0 with
      | mk argResult middle =>
        have argApprox := bindingsIH ea1 g1 env extra s0 argResult middle
          ⟨hk, hr, argsUnique, related, approx, argsDisjoint, oracle, safe, envSafe, argsSafe, approxSafe, globalsSafe⟩
        rw [hr] at run
        cases argResult with
        | err error =>
          cases run
          have finalApprox := ApproxEvaluate.stateGlobalsApproxKnownListEvaluate xs (env ++ extra) s0
            (.err error) middle c [body] (ea1.map Prod.snd ++ aenv) g1 [(bodyExpr, bodyApprox)] g2
            ⟨hr, hb, safe, envSafe, argsSafe, bodyDisjoint, uniqueBoth, argApprox.1⟩
          exact ⟨finalApprox, by intro vs impossible; cases impossible⟩
        | val values =>
          have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals xs (env ++ extra) s0
            (.val values) middle ⟨hr, safe, argsSafe, envSafe⟩
          have valuesSafe : ∀ v ∈ values, vsgcFree v := by simpa [rsgcFree] using safety.2.1
          have nextUnique := uniqueSetGlobalsEvaluate xs [body] (env ++ extra) s0 middle (.val values) ⟨bodyUnique, hr⟩
          have nextDisjoint := mglobalsDisjointEvaluate s0 [body] xs (env ++ extra) (.val values) middle
            ⟨hr, safe, envSafe, argsSafe, swappedUnique, bodyDisjoint⟩
          have nextOracle := oracleGapproxDisjointLemma xs (env ++ extra) s0 (.val values) middle
            c aenv g0 ea1 g1 ⟨hr, hk, argsUnique, oracle⟩
          have optimizerSafe := PreserveSafety.knownPreservesEsgcFree c xs aenv g0 ea1 g1
            ⟨hk, argsSafe, approxSafe, globalsSafe⟩
          have extendedSafe : ∀ v ∈ (values ++ env) ++ extra, vsgcFree v := by
            intro v member
            rw [List.append_assoc] at member
            rcases List.mem_append.mp member with inValues | inEnv
            · exact valuesSafe v inValues
            · exact envSafe v inEnv
          have extendedApproxSafe : ∀ a ∈ ea1.map Prod.snd ++ aenv, valApproxSgcFree a := by
            intro a member
            rcases List.mem_append.mp member with fromArgs | fromEnv
            · exact optimizerSafe.2.1 a fromArgs
            · exact approxSafe a fromEnv
          have extendedRelated : List.Forall₂ ValApproxVal (ea1.map Prod.snd ++ aenv) (values ++ env) :=
            List.rel_append (argApprox.2 values rfl) related
          cases bodyRun : evaluate [body] ((values ++ env) ++ extra) middle with
          | mk bodyResult last =>
            have bodyResultApprox := bodyIH ea1 g1 hk.symm [(bodyExpr, bodyApprox)] g2
              (values ++ env) extra middle bodyResult last
              ⟨hb, bodyRun, nextUnique, extendedRelated, argApprox.1, nextDisjoint, nextOracle, safety.1,
                extendedSafe, bodySafe, extendedApproxSafe, optimizerSafe.2.2⟩
            change evaluate [body] (values ++ (env ++ extra)) middle = (res, s) at run
            rw [← List.append_assoc, bodyRun] at run
            cases bodyResult <;> cases run <;> exact bodyResultApprox

end Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Let
