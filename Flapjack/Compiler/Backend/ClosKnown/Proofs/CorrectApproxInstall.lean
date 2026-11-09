module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxCall

@[expose] public section


/-! Installation case of known-function approximation correctness. -/
namespace Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Install
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Dynamic-installation operation case of the original approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxOpInstall {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.op trace .install xs] aenv g0 = (eas, g) ∧
      evaluate [.op trace .install xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.op trace .install xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.op trace .install xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.op trace .install xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  rcases h with ⟨known, run, unique, related, approx, disjoint, oracle, safe, envSafe, exprSafe, approxSafe, globalsSafe⟩
  have callRun := run
  have argsUnique : uniqueSetGlobals xs s0.compileOracle := by
    simpa [uniqueSetGlobals, elistGlobals_append, elistGlobals, setGlobals, opGlobalBag,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using unique
  have argsDisjoint : mglobalsDisjoint s0.globals xs := by
    simpa [mglobalsDisjoint, elistGlobals, setGlobals, opGlobalBag,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using disjoint
  have argsSafe : ∀ e ∈ xs, esgcFree e := by
    have h := exprSafe (.op trace .install xs) (by simp)
    simpa [esgcFree, esgcFreeList_iff] using h
  cases hk : knownListTotal c xs aenv g0 with
  | mk ea g1 =>
    rw [knownListTotal_op, hk] at known
    simp [knownOpHOL] at known
    rcases known with ⟨rfl, rfl⟩
    have resultRel : ∀ vs, res = .val vs → List.Forall₂ ValApproxVal [.other] vs := by
      intro vs eq
      have valueRun : evaluate [.op trace .install xs] (env ++ extra) s0 = (.val vs, s) := by
        simpa [eq] using callRun
      obtain ⟨v, rfl⟩ := evaluate_singleton_value (.op trace .install xs) (env ++ extra) s0 s vs valueRun
      exact .cons (.other v) .nil
    rw [evaluate, fixClock_evaluate] at run
    cases hr : evaluate xs (env ++ extra) s0 with
    | mk argResult middle =>
      have argApprox := argsIH ea g1 env extra s0 argResult middle
        ⟨hk, hr, argsUnique, related, approx, argsDisjoint, oracle, safe, envSafe, argsSafe, approxSafe, globalsSafe⟩
      rw [hr] at run
      cases argResult with
      | err error => cases run; exact ⟨argApprox.1, resultRel⟩
      | val values =>
        have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals xs (env ++ extra) s0
          (.val values) middle ⟨hr, safe, argsSafe, envSafe⟩
        have middleOracle := oracleGapproxDisjointLemma xs (env ++ extra) s0 (.val values) middle
          c aenv g0 ea g1 ⟨hr, hk, argsUnique, oracle⟩
        dsimp only at run
        cases hi : doInstall values.reverse middle with
        | mk installResult installed =>
          rw [hi] at run
          cases installResult with
          | err error =>
            have unchanged := (doInstallErrorSafety values.reverse middle installed error safety.1 hi).2.2.choose_spec.2
            cases run
            exact ⟨by simpa [stateGlobalsApprox, unchanged] using argApprox.1, resultRel⟩
          | val program =>
            have installSafe := doInstallSsgc values.reverse middle program installed ⟨hi, safety.1⟩
            have programDisjoint : gapproxDisjoint g1 program := by
              have pref := (oracleGapproxDisjointFirstN g1 middle.compileOracle).mp middleOracle 1
              simpa [installSafe.2.2.2.2.1] using pref
            have installedOracle : oracleGapproxDisjoint g1 installed.compileOracle := by
              rw [installSafe.2.2.2.1]
              exact oracleGapproxDisjointShift g1 middle.compileOracle middleOracle 1
            have installedApprox : stateGlobalsApprox installed g1 := by
              intro i v a ⟨found, lookup⟩
              have before := installSafe.2.2.2.2.2.2 i v ⟨found, by simp⟩
              exact argApprox.1 i v a ⟨before, lookup⟩
            cases he : evaluate program [] installed with
            | mk evalResult final =>
              have finalApprox := ApproxRuntime.stateGlobalsApproxEvaluateDisjoint program [] installed evalResult final g1
                he installSafe.1 (by simp) installSafe.2.1 programDisjoint installedOracle installedApprox
              dsimp only at run
              rw [he] at run
              cases evalResult <;> cases run <;> exact ⟨finalApprox, resultRel⟩

end Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Install
