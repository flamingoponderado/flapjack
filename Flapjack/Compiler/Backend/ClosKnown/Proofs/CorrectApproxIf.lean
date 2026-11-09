module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxHandle

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


/-! Conditional case of known-function approximation correctness. -/
namespace Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.If
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Conditional case of the original approximation theorem, with its three
source induction hypotheses in optimizer traversal order. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxIf {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (cond yes no : ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (noIH : ∀ (ea1 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox)
      (ea2 : List (ClosLang.Exp × ValApprox)) (g2 : Spt ValApprox),
      (ea1, g1) = knownListTotal c [cond] aenv g0 ∧ (ea2, g2) = knownListTotal c [yes] aenv g1 →
      KnownApproxInvariant C F c [no] aenv g2)
    (yesIH : ∀ (ea1 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox),
      (ea1, g1) = knownListTotal c [cond] aenv g0 → KnownApproxInvariant C F c [yes] aenv g1)
    (condIH : KnownApproxInvariant C F c [cond] aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.ifThenElse trace cond yes no] aenv g0 = (eas, g) ∧
      evaluate [.ifThenElse trace cond yes no] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.ifThenElse trace cond yes no] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.ifThenElse trace cond yes no] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.ifThenElse trace cond yes no], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  rcases h with ⟨known, run, unique, related, approx, disjoint, oracle, safe, envSafe, exprSafe, approxSafe, globalsSafe⟩
  have uniqueAll : uniqueSetGlobals ([cond] ++ ([yes] ++ [no])) s0.compileOracle := by
    intro n i
    have bound := unique n i
    simp only [elistGlobals_append, elistGlobals, setGlobals, FlatProps.unionGlobalBag,
      FlatProps.emptyGlobalBag, Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag] at bound ⊢
    omega
  have ⟨condUnique, branchesUnique, swappedUnique⟩ := Cons.uniqueParts [cond] ([yes] ++ [no]) s0.compileOracle uniqueAll
  have ⟨condDisjoint, yesDisjoint, noDisjoint⟩ :=
    (mglobalsDisjointRw s0.globals cond yes cond yes no [] trace .install [] none none [] 0 0).2.2.2.1.mp disjoint
  have branchesDisjoint : mglobalsDisjoint s0.globals ([yes] ++ [no]) :=
    (mglobalsDisjointRw s0.globals yes no yes yes yes [] trace .install [] none none [] 0 0).1.mpr
      ⟨yesDisjoint, noDisjoint⟩
  have allSafe := exprSafe (.ifThenElse trace cond yes no) (by simp)
  simp only [esgcFree] at allSafe
  have condSafe : ∀ e ∈ [cond], esgcFree e := by simpa using allSafe.1
  have yesSafe : ∀ e ∈ [yes], esgcFree e := by simpa using allSafe.2.1
  have noSafe : ∀ e ∈ [no], esgcFree e := by simpa using allSafe.2.2
  cases hc : knownListTotal c [cond] aenv g0 with
  | mk ea1 g1 =>
    obtain ⟨ec, ac, eq1⟩ := knownListTotal_single_result c cond aenv g0 g1 ea1 hc
    subst ea1
    cases hy : knownListTotal c [yes] aenv g1 with
    | mk ea2 g2 =>
      obtain ⟨ey, ay, eq2⟩ := knownListTotal_single_result c yes aenv g1 g2 ea2 hy
      subst ea2
      cases hn : knownListTotal c [no] aenv g2 with
      | mk ea3 g3 =>
        obtain ⟨en, an, eq3⟩ := knownListTotal_single_result c no aenv g2 g3 ea3 hn
        subst ea3
        have branchesKnown : knownListTotal c ([yes] ++ [no]) aenv g1 = ([(ey, ay), (en, an)], g3) := by
          rw [show [yes] ++ [no] = yes :: no :: [] by rfl, knownListTotal_cons_cons, hy]
          dsimp only
          rw [hn]
          rfl
        rw [knownListTotal_if, hc] at known
        dsimp only at known
        rw [hy] at known
        dsimp only at known
        rw [hn] at known
        simp [knownSourceHead] at known
        rcases known with ⟨rfl, rfl⟩
        rw [evaluate, fixClock_evaluate] at run
        cases hr : evaluate [cond] (env ++ extra) s0 with
        | mk condResult middle =>
          have condApprox := condIH [(ec, ac)] g1 env extra s0 condResult middle
            ⟨hc, hr, condUnique, related, approx, condDisjoint, oracle, safe, envSafe, condSafe, approxSafe, globalsSafe⟩
          have skipBranches : stateGlobalsApprox middle g3 :=
            ApproxEvaluate.stateGlobalsApproxKnownListEvaluate [cond] (env ++ extra) s0 condResult middle
              c ([yes] ++ [no]) aenv g1 [(ey, ay), (en, an)] g3
              ⟨hr, branchesKnown, safe, envSafe, condSafe, branchesDisjoint, uniqueAll, condApprox.1⟩
          rw [hr] at run
          cases condResult with
          | err error =>
            cases run
            exact ⟨skipBranches, by intro vs impossible; cases impossible⟩
          | val values =>
            have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals [cond] (env ++ extra) s0
              (.val values) middle ⟨hr, safe, condSafe, envSafe⟩
            have middleUnique := uniqueSetGlobalsEvaluate [cond] ([yes] ++ [no]) (env ++ extra) s0 middle
              (.val values) ⟨branchesUnique, hr⟩
            have ⟨yesUnique, noUnique, noYesUnique⟩ := Cons.uniqueParts [yes] [no] middle.compileOracle middleUnique
            have middleDisjoint := mglobalsDisjointEvaluate s0 ([yes] ++ [no]) [cond] (env ++ extra)
              (.val values) middle ⟨hr, safe, envSafe, condSafe, swappedUnique, branchesDisjoint⟩
            have ⟨yesDisjoint', noDisjoint'⟩ :=
              (mglobalsDisjointRw middle.globals yes no yes yes yes [] trace .install [] none none [] 0 0).1.mp middleDisjoint
            have middleOracle := oracleGapproxDisjointLemma [cond] (env ++ extra) s0 (.val values) middle
              c aenv g0 [(ec, ac)] g1 ⟨hr, hc, condUnique, oracle⟩
            have middleGlobalsSafe := (PreserveSafety.knownPreservesEsgcFree c [cond] aenv g0
              [(ec, ac)] g1 ⟨hc, condSafe, approxSafe, globalsSafe⟩).2.2
            obtain ⟨value, rfl⟩ := evaluate_singleton_value cond (env ++ extra) s0 middle values hr
            change (match asBool value with
              | none => (.err (.abort .typeError), middle)
              | some true => evaluate [yes] (env ++ extra) middle
              | some false => evaluate [no] (env ++ extra) middle) = (res, s) at run
            cases hb : asBool value with
            | none =>
              simp [hb] at run
              rcases run with ⟨rfl, rfl⟩
              exact ⟨skipBranches, by intro vs impossible; cases impossible⟩
            | some b =>
              cases b with
              | false =>
                simp only [hb] at run
                have g2Approx := ApproxEvaluate.stateGlobalsApproxKnownDisjoint c [yes] aenv g1 [(ey, ay)] g2 middle
                  ⟨hy, yesDisjoint', condApprox.1⟩
                have g2Safe := (PreserveSafety.knownPreservesEsgcFree c [yes] aenv g1
                  [(ey, ay)] g2 ⟨hy, yesSafe, approxSafe, middleGlobalsSafe⟩).2.2
                have g2OracleShift := oracleGapproxDisjointShiftUnique c [yes] aenv g1 [(ey, ay)] g2 middle 0
                  ⟨hy, yesUnique, middleOracle⟩
                have g2Oracle : oracleGapproxDisjoint g2 middle.compileOracle := by
                  rw [shiftSeqZero] at g2OracleShift
                  exact g2OracleShift
                cases hnRun : evaluate [no] (env ++ extra) middle with
                | mk noResult last =>
                  have noApprox := noIH [(ec, ac)] g1 [(ey, ay)] g2 ⟨hc.symm, hy.symm⟩
                    [(en, an)] g3 env extra middle noResult last
                    ⟨hn, hnRun, noUnique, related, g2Approx, noDisjoint', g2Oracle, safety.1,
                      envSafe, noSafe, approxSafe, g2Safe⟩
                  rw [hnRun] at run
                  cases noResult with
                  | err error => cases run; exact ⟨noApprox.1, by intro vs impossible; cases impossible⟩
                  | val returned =>
                    cases run
                    refine ⟨noApprox.1, ?_⟩
                    intro vs eq
                    cases eq
                    simpa using Handle.mergeSingletonRight ay an returned (by simpa using noApprox.2 returned rfl)
              | true =>
                simp only [hb] at run
                cases hyRun : evaluate [yes] (env ++ extra) middle with
                | mk yesResult last =>
                  have yesApprox := yesIH [(ec, ac)] g1 hc.symm [(ey, ay)] g2 env extra middle yesResult last
                    ⟨hy, hyRun, yesUnique, related, condApprox.1, yesDisjoint', middleOracle, safety.1,
                      envSafe, yesSafe, approxSafe, middleGlobalsSafe⟩
                  have finalApprox := ApproxEvaluate.stateGlobalsApproxKnownListEvaluate [yes] (env ++ extra) middle
                    yesResult last c [no] aenv g2 [(en, an)] g3
                    ⟨hyRun, hn, safety.1, envSafe, yesSafe, noDisjoint', middleUnique, yesApprox.1⟩
                  rw [hyRun] at run
                  cases yesResult with
                  | err error => cases run; exact ⟨finalApprox, by intro vs impossible; cases impossible⟩
                  | val returned =>
                    cases run
                    refine ⟨finalApprox, ?_⟩
                    intro vs eq
                    cases eq
                    simpa using Handle.mergeSingletonLeft ay an returned (by simpa using yesApprox.2 returned rfl)

end Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.If
