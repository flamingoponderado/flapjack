module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxCall

@[expose] public section


/-! Thunk-forcing case of known-function approximation correctness. -/
namespace Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Force
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- A safe thunk store yields a safe thunk payload. This is Flapjack proof
infrastructure. -/
private theorem destThunkValueSafe {C F : Type} (values : List ClosSem.Value)
    (s : State C F) (mode : AstHOL.ThunkMode) (value : ClosSem.Value)
    (safe : ssgcFree s) (found : destThunk values s.refs = .isThunk mode value) : vsgcFree value := by
  unfold ClosSem.destThunk at found
  repeat' split at found
  all_goals simp_all
  exact safe.2.2.1 _ _ _ (by assumption)

/-- Thunk-forcing operation case of the original approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxOpForce {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.op trace (.thunkOp .forceThunk) xs] aenv g0 = (eas, g) ∧
      evaluate [.op trace (.thunkOp .forceThunk) xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.op trace (.thunkOp .forceThunk) xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.op trace (.thunkOp .forceThunk) xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.op trace (.thunkOp .forceThunk) xs], esgcFree e) ∧
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
    have h := exprSafe (.op trace (.thunkOp .forceThunk) xs) (by simp)
    simpa [esgcFree, esgcFreeList_iff] using h
  cases hk : knownListTotal c xs aenv g0 with
  | mk ea g1 =>
    rw [knownListTotal_op, hk] at known
    simp [knownOpHOL] at known
    rcases known with ⟨rfl, rfl⟩
    have resultRel : ∀ vs, res = .val vs → List.Forall₂ ValApproxVal [.other] vs := by
      intro vs eq
      have valueRun : evaluate [.op trace (.thunkOp .forceThunk) xs] (env ++ extra) s0 = (.val vs, s) := by
        simpa [eq] using callRun
      obtain ⟨v, rfl⟩ := evaluate_singleton_value (.op trace (.thunkOp .forceThunk) xs)
        (env ++ extra) s0 s vs valueRun
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
        cases inspected : destThunk values middle.refs with
        | badRef | notThunk => simp [inspected] at run; rcases run with ⟨rfl, rfl⟩; exact ⟨argApprox.1, resultRel⟩
        | isThunk mode value =>
          have valueSafe := destThunkValueSafe values middle mode value safety.1 inspected
          cases mode with
          | evaluated => simp [inspected] at run; rcases run with ⟨rfl, rfl⟩; exact ⟨argApprox.1, resultRel⟩
          | notEvaluated =>
            simp only [inspected] at run
            cases he : evaluate [appUnit (.var .none 0)] [value] middle with
            | mk forceResult last =>
              have forceSafe : ∀ e ∈ [appUnit (.var .none 0)], esgcFree e := by
                simp [appUnit, esgcFree, esgcFreeList]
              have forceEmpty : elistGlobals [appUnit (.var .none 0)] = FlatProps.emptyGlobalBag := by
                funext i
                simp [appUnit, elistGlobals, setGlobals, opGlobalBag, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag]
              have lastApprox := ApproxRuntime.stateGlobalsApproxEvaluateEmpty [appUnit (.var .none 0)] [value]
                middle forceResult last g1 he safety.1 (by simpa using valueSafe) forceSafe forceEmpty middleOracle argApprox.1
              rw [he] at run
              cases forceResult with
              | err error => cases run; exact ⟨lastApprox, resultRel⟩
              | val forced =>
                dsimp only at run
                cases hu : updateThunk values last.refs forced with
                | none => simp [hu] at run; rcases run with ⟨rfl, rfl⟩; exact ⟨lastApprox, resultRel⟩
                | some refs =>
                  simp [hu] at run
                  rcases run with ⟨rfl, rfl⟩
                  exact ⟨by simpa [stateGlobalsApprox] using lastApprox, resultRel⟩

end Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Force
