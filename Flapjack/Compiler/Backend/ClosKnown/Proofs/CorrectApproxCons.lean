import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApprox
import Flapjack.Compiler.Backend.ClosKnown.Proofs.PreserveSafetyTotal
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength

/-! Sequential case of known-function approximation correctness. -/
namespace Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Cons
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Removing either initial list or exchanging their order preserves the
source global-write uniqueness condition. Flapjack induction infrastructure. -/
theorem uniqueParts {α β : Type} (xs ys : List ClosLang.Exp)
    (co : Nat → α × List ClosLang.Exp × β) (unique : uniqueSetGlobals (xs ++ ys) co) :
    uniqueSetGlobals xs co ∧ uniqueSetGlobals ys co ∧ uniqueSetGlobals (ys ++ xs) co := by
  refine ⟨?_, ?_, ?_⟩ <;> intro n i <;> have bound := unique n i <;>
    simp only [elistGlobals_append] at bound ⊢ <;> omega

/-- Sequential-list case of the original approximation theorem, with its
head and result-dependent tail induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxCons {C F : Type} (c : Config) (x y : ClosLang.Exp)
    (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (tailIH : ∀ (ea1 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox),
      (ea1, g1) = knownListTotal c [x] aenv g0 → KnownApproxInvariant C F c (y :: xs) aenv g1)
    (headIH : KnownApproxInvariant C F c [x] aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c (x :: y :: xs) aenv g0 = (eas, g) ∧
      evaluate (x :: y :: xs) (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals (x :: y :: xs) s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals (x :: y :: xs) ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ x :: y :: xs, esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  rcases h with ⟨known, run, unique, related, approx, disjoint, oracle, safe, envSafe, exprSafe, approxSafe, globalsSafe⟩
  have ⟨headUnique, tailUnique, swappedUnique⟩ := uniqueParts [x] (y :: xs) s0.compileOracle unique
  have ⟨headDisjoint, tailDisjoint⟩ :=
    (mglobalsDisjointRw s0.globals x y x x x xs .none .install [] none none [] 0 0).1.mp disjoint
  have headSafe : ∀ e ∈ [x], esgcFree e := by simpa using exprSafe x (by simp)
  have tailSafe : ∀ e ∈ y :: xs, esgcFree e := by
    intro e member
    exact exprSafe e (List.mem_cons_of_mem _ member)
  cases hk : knownListTotal c [x] aenv g0 with
  | mk headEas g1 =>
    obtain ⟨headExpr, headApprox, headEq⟩ := knownListTotal_single_result c x aenv g0 g1 headEas hk
    subst headEas
    cases ht : knownListTotal c (y :: xs) aenv g1 with
    | mk tailEas g2 =>
      rw [knownListTotal_cons_cons, hk] at known
      dsimp only at known
      rw [ht] at known
      simp only [Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      rw [evaluate, fixClock_evaluate] at run
      cases hr : evaluate [x] (env ++ extra) s0 with
      | mk headResult middle =>
        have headResultApprox := headIH [(headExpr, headApprox)] g1 env extra s0 headResult middle
          ⟨hk, hr, headUnique, related, approx, headDisjoint, oracle, safe, envSafe, headSafe, approxSafe, globalsSafe⟩
        rw [hr] at run
        cases headResult with
        | err error =>
          cases run
          have finalApprox := ApproxEvaluate.stateGlobalsApproxKnownListEvaluate [x] (env ++ extra) s0
            (.err error) middle c (y :: xs) aenv g1 tailEas g2
            ⟨hr, ht, safe, envSafe, headSafe, tailDisjoint, unique, headResultApprox.1⟩
          exact ⟨finalApprox, by intro vs impossible; cases impossible⟩
        | val values =>
          obtain ⟨value, rfl⟩ := evaluate_singleton_value x (env ++ extra) s0 middle values hr
          have middleSafe := (EvaluateGlobalsPort.Total.evaluateChangedGlobals [x] (env ++ extra) s0
            (.val [value]) middle ⟨hr, safe, headSafe, envSafe⟩).1
          have nextUnique := uniqueSetGlobalsEvaluate [x] (y :: xs) (env ++ extra) s0 middle (.val [value])
            ⟨tailUnique, hr⟩
          have nextDisjoint := mglobalsDisjointEvaluate s0 (y :: xs) [x] (env ++ extra) (.val [value]) middle
            ⟨hr, safe, envSafe, headSafe, swappedUnique, tailDisjoint⟩
          have nextOracle := oracleGapproxDisjointLemma [x] (env ++ extra) s0 (.val [value]) middle
            c aenv g0 [(headExpr, headApprox)] g1 ⟨hr, hk, headUnique, oracle⟩
          have nextGlobalsSafe := (PreserveSafety.knownPreservesEsgcFree c [x] aenv g0
            [(headExpr, headApprox)] g1 ⟨hk, headSafe, approxSafe, globalsSafe⟩).2.2
          cases tr : evaluate (y :: xs) (env ++ extra) middle with
          | mk tailResult last =>
            have tailResultApprox := tailIH [(headExpr, headApprox)] g1 hk.symm tailEas g2 env extra middle tailResult last
              ⟨ht, tr, nextUnique, related, headResultApprox.1, nextDisjoint, nextOracle, middleSafe,
                envSafe, tailSafe, approxSafe, nextGlobalsSafe⟩
            rw [tr] at run
            cases tailResult with
            | err error =>
              cases run
              exact ⟨tailResultApprox.1, by intro vs impossible; cases impossible⟩
            | val tailValues =>
              cases run
              refine ⟨tailResultApprox.1, ?_⟩
              intro vs eq
              cases eq
              have firstRelated := headResultApprox.2 [value] rfl
              have restRelated := tailResultApprox.2 tailValues rfl
              simp only [List.map_append, List.map_cons, List.map_nil]
              cases firstRelated with
              | cons hv _ => exact .cons hv restRelated

end Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Cons
