import Flapjack.Compiler.Backend.RegAlloc.ProductionCoalesce
import Flapjack.Compiler.Backend.RegAlloc.ProductionSpill
import Flapjack.Compiler.Backend.RegAlloc.ProductionFreeze
import Flapjack.Compiler.Backend.RegAlloc.Proofs.DoAlloc1Success

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- Post-state invariants are obtained by identifying the actual/native
transition proof with the independently established source success theorem.
This is proof infrastructure, not a HOL declaration or an assumed simulator. -/
private theorem source_post (action : M State Bool StateException)
    (native result : State) (value : Bool)
    (run : action native = (.success value, result))
    (source : ∃ final output, action native = (.success output, final) ∧
      goodRaState final ∧ isSubgraph native.adj_ls final.adj_ls ∧
      native.dim = final.dim ∧ native.node_tag = final.node_tag) :
    goodRaState result ∧ native.dim = result.dim := by
  obtain ⟨final, output, sourceRun, good, _, dimension, _⟩ := source
  have equality : result = final := congrArg Prod.snd (run.symm.trans sourceRun)
  exact ⟨equality.symm ▸ good, by simpa only [equality] using dimension⟩


private theorem simplify_step (limit : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result, doSimplify limit native = (.success (cakeDoSimplify limit production).1, result) ∧
      goodRaState result ∧ native.dim = result.dim ∧
      ProductionStateRel result (cakeDoSimplify limit production).2 := by
  obtain ⟨result, run, represented⟩ := doSimplify_production limit related good
  have facts := source_post (doSimplify limit) native result _ run (doSimplifySuccess limit native good)
  exact ⟨result, run, facts.1, facts.2, represented⟩

private theorem coalesce_step (limit : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result, doCoalesce limit native = (.success (cakeDoCoalesce limit production).1, result) ∧
      goodRaState result ∧ native.dim = result.dim ∧
      ProductionStateRel result (cakeDoCoalesce limit production).2 := by
  obtain ⟨result, run, represented⟩ := doCoalesce_production limit related good
  have facts := source_post (doCoalesce limit) native result _ run (doCoalesceSuccess limit native good)
  exact ⟨result, run, facts.1, facts.2, represented⟩

private theorem prefreeze_step (limit : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result, doPrefreeze limit native = (.success (cakeDoPrefreeze limit production).1, result) ∧
      goodRaState result ∧ native.dim = result.dim ∧
      ProductionStateRel result (cakeDoPrefreeze limit production).2 := by
  obtain ⟨result, run, represented⟩ := doPrefreeze_production limit related good
  have facts := source_post (doPrefreeze limit) native result _ run (doPrefreezeSuccess limit native good)
  exact ⟨result, run, facts.1, facts.2, represented⟩

private theorem freeze_step (limit : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result, doFreeze limit native = (.success (cakeDoFreeze limit production).1, result) ∧
      goodRaState result ∧ native.dim = result.dim ∧
      ProductionStateRel result (cakeDoFreeze limit production).2 := by
  obtain ⟨result, run, represented⟩ := doFreeze_production limit related good
  have facts := source_post (doFreeze limit) native result _ run (doFreezeSuccess limit native good)
  exact ⟨result, run, facts.1, facts.2, represented⟩

/-- Complete actual phase dispatch: every intermediate good state and cost
map dimension is derived from the original native source invariant. This is
Flapjack implementation correspondence, not a separate HOL declaration. -/
theorem doStep_production (entries : Option (NatInfoMap Nat)) (limit : Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result,
      doStep (entries.map sptFromAList) limit native =
        (.success (cakeDoStep (entries.map (cakeSpillCostMap production.dim)) limit production).1, result) ∧
      ProductionStateRel result
        (cakeDoStep (entries.map (cakeSpillCostMap production.dim)) limit production).2 := by
  obtain ⟨first, firstRun, firstGood, firstDim, firstRel⟩ := simplify_step limit related good
  generalize actualFirstEq : cakeDoSimplify limit production = actualFirst at *
  cases firstChoice : actualFirst.1 with
  | true =>
    refine ⟨first, ?_, ?_⟩
    · simp [doStep, Translator.Monadic.MonadBase.bind, firstRun, cakeDoStep,
        actualFirstEq, firstChoice, ret]
    · simpa only [cakeDoStep, actualFirstEq, firstChoice, ↓reduceIte] using firstRel
  | false =>
    obtain ⟨second, secondRun, secondGood, secondDim, secondRel⟩ := coalesce_step limit firstRel firstGood
    generalize actualSecondEq : cakeDoCoalesce limit actualFirst.2 = actualSecond at *
    cases secondChoice : actualSecond.1 with
    | true =>
      refine ⟨second, ?_, ?_⟩
      · simp [doStep, Translator.Monadic.MonadBase.bind, firstRun, secondRun, cakeDoStep,
          actualFirstEq, actualSecondEq, firstChoice, secondChoice, ret]
      · simpa only [cakeDoStep, actualFirstEq, actualSecondEq, firstChoice, secondChoice,
          Bool.false_eq_true, ↓reduceIte] using secondRel
    | false =>
      obtain ⟨third, thirdRun, thirdGood, thirdDim, thirdRel⟩ := prefreeze_step limit secondRel secondGood
      generalize actualThirdEq : cakeDoPrefreeze limit actualSecond.2 = actualThird at *
      cases thirdChoice : actualThird.1 with
      | true =>
        refine ⟨third, ?_, ?_⟩
        · simp [doStep, Translator.Monadic.MonadBase.bind, firstRun, secondRun, thirdRun, cakeDoStep,
            actualFirstEq, actualSecondEq, actualThirdEq, firstChoice, secondChoice, thirdChoice, ret]
        · simpa only [cakeDoStep, actualFirstEq, actualSecondEq, actualThirdEq,
            firstChoice, secondChoice, thirdChoice, Bool.false_eq_true, ↓reduceIte] using thirdRel
      | false =>
        obtain ⟨fourth, fourthRun, fourthGood, fourthDim, fourthRel⟩ := freeze_step limit thirdRel thirdGood
        generalize actualFourthEq : cakeDoFreeze limit actualThird.2 = actualFourth at *
        cases fourthChoice : actualFourth.1 with
        | true =>
          refine ⟨fourth, ?_, ?_⟩
          · simp [doStep, Translator.Monadic.MonadBase.bind, firstRun, secondRun, thirdRun, fourthRun,
              cakeDoStep, actualFirstEq, actualSecondEq, actualThirdEq, actualFourthEq,
              firstChoice, secondChoice, thirdChoice, fourthChoice, ret]
          · simpa only [cakeDoStep, actualFirstEq, actualSecondEq, actualThirdEq, actualFourthEq,
              firstChoice, secondChoice, thirdChoice, fourthChoice, Bool.false_eq_true, ↓reduceIte] using fourthRel
        | false =>
          obtain ⟨result, spillRun, represented⟩ := doSpill_production entries limit fourthRel fourthGood
          have dimension : actualFourth.2.dim = production.dim :=
            fourthRel.dimension.trans (fourthDim.symm.trans (thirdDim.symm.trans
              (secondDim.symm.trans (firstDim.symm.trans related.dimension.symm))))
          rw [dimension] at spillRun represented
          refine ⟨result, ?_, ?_⟩
          · simp [doStep, Translator.Monadic.MonadBase.bind, firstRun, secondRun, thirdRun, fourthRun,
              cakeDoStep, actualFirstEq, actualSecondEq, actualThirdEq, actualFourthEq,
              firstChoice, secondChoice, thirdChoice, fourthChoice, spillRun, ret]
          · simpa only [cakeDoStep, actualFirstEq, actualSecondEq, actualThirdEq, actualFourthEq,
              firstChoice, secondChoice, thirdChoice, fourthChoice, Bool.false_eq_true, ↓reduceIte] using represented

/-- The whole dispatch preserves the original good state and dimension as
well as every actual/native field. Source success supplies these facts; callers
need no desired post-state premise. This is Flapjack-only infrastructure. -/
theorem doStep_production_invariant (entries : Option (NatInfoMap Nat)) (limit : Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result,
      doStep (entries.map sptFromAList) limit native =
        (.success (cakeDoStep (entries.map (cakeSpillCostMap production.dim)) limit production).1, result) ∧
      goodRaState result ∧ native.dim = result.dim ∧
      ProductionStateRel result
        (cakeDoStep (entries.map (cakeSpillCostMap production.dim)) limit production).2 := by
  obtain ⟨result, run, represented⟩ := doStep_production entries limit related good
  obtain ⟨output, final, sourceRun, finalGood, _, dimension, _⟩ :=
    doStepSuccess (entries.map sptFromAList) limit native good
  have equality : result = final := congrArg Prod.snd (run.symm.trans sourceRun)
  exact ⟨result, run, equality.symm ▸ finalGood,
    by simpa only [equality] using dimension, represented⟩

/-- All-fuel correspondence for the actual repeated phase. The same source
cost associations are used throughout; invariant dimension discharges the
recursive array-map codec identity. This theorem connects the executed array
implementation to the native loop and has no separate HOL original. -/
theorem rptDoStep_production (entries : Option (NatInfoMap Nat)) (limit fuel : Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result,
      rptDoStep (entries.map sptFromAList) limit fuel native = (.success (), result) ∧
      goodRaState result ∧ native.dim = result.dim ∧
      ProductionStateRel result
        (cakeRptDoStep (entries.map (cakeSpillCostMap production.dim)) limit fuel production) := by
  induction fuel generalizing native production with
  | zero =>
    exact ⟨native, rfl, good, rfl, related⟩
  | succ fuel ih =>
    obtain ⟨step, stepRun, stepGood, stepDim, stepRel⟩ :=
      doStep_production_invariant entries limit related good
    have dimension :
        (cakeDoStep (entries.map (cakeSpillCostMap production.dim)) limit production).2.dim = production.dim :=
      stepRel.dimension.trans (stepDim.symm.trans related.dimension.symm)
    cases choice : (cakeDoStep (entries.map (cakeSpillCostMap production.dim)) limit production).1 with
    | false =>
      refine ⟨step, ?_, stepGood, stepDim, ?_⟩
      · simp only [rptDoStep, Translator.Monadic.MonadBase.bind, stepRun, choice,
          Bool.false_eq_true, ↓reduceIte, ret]
      · simpa only [cakeRptDoStep, choice, Bool.false_eq_true, ↓reduceIte] using stepRel
    | true =>
      obtain ⟨result, run, resultGood, resultDim, represented⟩ := ih stepRel stepGood
      rw [dimension] at represented
      refine ⟨result, ?_, resultGood, stepDim.trans resultDim, ?_⟩
      · simp only [rptDoStep, Translator.Monadic.MonadBase.bind, stepRun, choice, ↓reduceIte, run]
      · simpa only [cakeRptDoStep, choice, ↓reduceIte] using represented

end Flapjack.RegAlloc
