module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.Simulation
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SubsptComposition
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxCons

@[expose] public section


/-! Sequential-list case of the known-function semantic simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Cons
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint SubsptComposition
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Sequential-list case of the original optimizer simulation, with the
source evaluator's head and successful-head tail induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0Cons {C F : Type} (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env1full : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F)
    (tailIH : ∀ (headResult : Result (List ClosSem.Value) ClosSem.Value)
      (middle : State (Spt ValApprox × C) F) (headValues : List ClosSem.Value),
      evaluate [x] env1full s0 = (headResult, middle) ∧ headResult = .val headValues →
      KnownSimulationAt (y :: xs) env1full middle)
    (headIH : KnownSimulationAt [x] env1full s0) :
    KnownSimulationAt (x :: y :: xs) env1full s0 := by
  intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
  obtain ⟨run, known, state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
    exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
    sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
  have ⟨headUnique, tailUnique, swappedUnique⟩ := CorrectApprox.Cons.uniqueParts [x] (y :: xs) s0.compileOracle unique
  have ⟨headDisjoint, tailDisjoint⟩ :=
    (mglobalsDisjointRw s0.globals x y x x x xs .none .install [] none none [] 0 0).1.mp disjoint
  have syntaxParts : everyFnVarsNone [x] ∧ everyFnVarsNone (y :: xs) := by
    simpa [everyFnVarsNone] using inputSyntax
  have headSyntax := syntaxParts.1
  have tailSyntax := syntaxParts.2
  have headSafe : ∀ e ∈ [x], esgcFree e := by simpa using exprSafe x (by simp)
  have tailSafe : ∀ e ∈ y :: xs, esgcFree e := by
    intro e member
    exact exprSafe e (List.mem_cons_of_mem _ member)
  have ⟨headFree, tailFree⟩ := (fvMaxCons env1.length x (y :: xs)).1 free
  have bagDisjoint : ∀ i, elistGlobals [x] i = 0 ∨ elistGlobals (y :: xs) i = 0 := by
    intro i
    have bound := unique 0 i
    simp only [elistGlobals_append, elistGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag,
      Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag] at bound ⊢
    omega
  cases hk : knownListTotal c [x] aenv g0 with
  | mk headEas g1 =>
    obtain ⟨xe, xa, eq⟩ := knownListTotal_single_result c x aenv g0 g1 headEas hk
    subst headEas
    cases ht : knownListTotal c (y :: xs) aenv g1 with
    | mk tailEas g2 =>
      have tailNonempty : tailEas ≠ [] := by
        intro empty
        subst tailEas
        have len := knownListTotal_length c (y :: xs) aenv g1
        rw [ht] at len
        simp at len
      rw [knownListTotal_cons_cons, hk] at known
      dsimp only at known
      rw [ht] at known
      simp only [Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      have ⟨subHead, subTail⟩ := subsptKnownElistGlobals c [x] aenv g0 [(xe, xa)] g1
        (y :: xs) aenv tailEas g2 ⟨hk, ht, sub0, bagDisjoint⟩
      have subHeadNext : sptSubspt g1 (nextG s0) := sptSubsptTrans _ _ _ ⟨subTail, sub1⟩
      cases hr : evaluate [x] env1full s0 with
      | mk headResult middle =>
        have headNoType : headResult ≠ .err (.abort .typeError) := by
          intro eq
          subst headResult
          rw [evaluate, fixClock_evaluate, hr] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact noType rfl
        have step := headIH headResult middle env1 xenv1 env2 xenv2 t0 c g0 g1 aenv [(xe, xa)]
          ⟨hr, hk, state, headSyntax, coSyntax, headDisjoint, oracle, stateOracleDisjoint,
            headSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
            subHead, subHeadNext, mono, headFree, envRel, headUnique, stateOracle, envEq, headNoType⟩
        obtain ⟨targetHeadResult, targetMiddle, targetHeadRun, headRel, midState, midGlobals, midStateOracle, midOracle⟩ := step
        have targetHeadRun' : evaluate [xe] (env2 ++ xenv2) t0 = (targetHeadResult, targetMiddle) := by
          simpa using targetHeadRun
        rw [evaluate, fixClock_evaluate, hr] at run
        cases headResult with
        | err error =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          cases targetHeadResult with
          | val values => simp [resultRel] at headRel
          | err error2 =>
            refine ⟨.err error2, targetMiddle, ?_, headRel, midState, midGlobals, midStateOracle, midOracle⟩
            cases tailEas with
            | nil => contradiction
            | cons entry rest =>
              simp only [List.map_cons, List.cons_append, List.nil_append]
              rw [evaluate, fixClock_evaluate, targetHeadRun']
        | val headValues =>
          obtain ⟨head, rfl⟩ := evaluate_singleton_value x env1full s0 middle headValues hr
          cases targetHeadResult with
          | err error => simp [resultRel] at headRel
          | val targetValues =>
            obtain ⟨targetHead, rfl⟩ := evaluate_singleton_value xe (env2 ++ xenv2) t0 targetMiddle targetValues targetHeadRun'
            have valuesRel : ValueRel c (nextG middle) head targetHead := by
              cases headRel with | cons rel _ => exact rel
            have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals [x] env1full s0 (.val [head]) middle
              ⟨hr, safe, headSafe, envSafe⟩
            have nextUnique := uniqueSetGlobalsEvaluate [x] (y :: xs) env1full s0 middle (.val [head]) ⟨tailUnique, hr⟩
            have nextDisjoint := mglobalsDisjointEvaluate s0 (y :: xs) [x] env1full (.val [head]) middle
              ⟨hr, safe, envSafe, headSafe, swappedUnique, tailDisjoint⟩
            have nextStateOracleDisjoint := stateOracleMglobalsDisjointEvaluate [x] env1full s0 (.val [head]) middle
              ⟨hr, safe, headSafe, envSafe, headUnique, headDisjoint, stateOracleDisjoint⟩
            obtain ⟨n, shifted⟩ := evaluateImpShiftSeq [x] env1full s0 (.val [head]) middle hr
            have nextCoSyntax : coEveryFnVarsNone middle.compileOracle := by
              rw [shifted]
              exact coEveryFnVarsNoneShift s0.compileOracle coSyntax n
            have nextOracleSafe : oracleStateSgcFree middle.compileOracle := by
              rw [shifted]
              exact oracleStateSgcFreeShift s0.compileOracle oracleSafe n
            have nextMono : oracleGapproxSubspt middle.compileOracle :=
              oracleGapproxSubsptEvaluate () [x] env1full s0 (.val [head]) middle ⟨mono, hr⟩
            have nextTree := nextGEvaluateSubspt [x] env1full s0 (.val [head]) middle ⟨mono, hr⟩
            have nextRel := valueRelListSubspt c (nextG s0) env1 env2 envRel (nextG middle) nextTree
            have nextSafe := (PreserveSafety.knownPreservesEsgcFree c [x] aenv g0 [(xe, xa)] g1
              ⟨hk, headSafe, approxSafe, globalSafe⟩).2.2
            cases tr : evaluate (y :: xs) env1full middle with
            | mk tailResult last =>
              have tailNoType : tailResult ≠ .err (.abort .typeError) := by
                intro eq
                subst tailResult
                simp [tr] at run
                rcases run with ⟨rfl, rfl⟩
                exact noType rfl
              have tailStep := tailIH (.val [head]) middle [head] ⟨hr, rfl⟩ tailResult last
                env1 xenv1 env2 xenv2 targetMiddle c g1 g2 aenv tailEas
                ⟨tr, ht, midState, tailSyntax, nextCoSyntax, nextDisjoint, midOracle, nextStateOracleDisjoint,
                  tailSafe, safety.1, envSafe, approxRel, nextOracleSafe, nextSafe, approxSafe, midGlobals,
                  subTail, sptSubsptTrans _ _ _ ⟨sub1, nextTree⟩, nextMono, tailFree, nextRel, nextUnique,
                  midStateOracle, envEq, tailNoType⟩
              obtain ⟨targetTailResult, targetLast, targetTailRun, tailRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := tailStep
              simp only [tr] at run
              cases tailResult with
              | err error =>
                simp at run
                rcases run with ⟨rfl, rfl⟩
                cases targetTailResult with
                | val values => simp [resultRel] at tailRel
                | err error2 =>
                  refine ⟨.err error2, targetLast, ?_, tailRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩
                  cases tailEas with
                  | nil => contradiction
                  | cons entry rest =>
                    simp only [List.map_cons, List.cons_append, List.nil_append] at targetTailRun ⊢
                    rw [evaluate, fixClock_evaluate, targetHeadRun', targetTailRun]
              | val tailValues =>
                simp at run
                rcases run with ⟨rfl, rfl⟩
                cases targetTailResult with
                | err error => simp [resultRel] at tailRel
                | val targetTailValues =>
                  have nextTreeFinal := nextGEvaluateSubspt (y :: xs) env1full middle (.val tailValues) last ⟨nextMono, tr⟩
                  have finalHeadRel := valueRelSubspt c (nextG middle) head targetHead (nextG last) ⟨valuesRel, nextTreeFinal⟩
                  refine ⟨.val (targetHead :: targetTailValues), targetLast, ?_, ?_, finalState, finalGlobals, finalOracle, finalDisjoint⟩
                  · cases tailEas with
                    | nil => contradiction
                    | cons entry rest =>
                      simp only [List.map_cons, List.cons_append, List.nil_append] at targetTailRun ⊢
                      rw [evaluate, fixClock_evaluate, targetHeadRun', targetTailRun]
                      simp
                  · exact .cons finalHeadRel tailRel

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Cons
