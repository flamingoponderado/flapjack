module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationCons

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


/-! Exception-handler case of the known-function semantic simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Handle
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint SubsptComposition
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Sparse-tree inclusion composes. This is Flapjack infrastructure. -/
private theorem subsptTrans {A : Type} (a b c : Spt A) (h1 : sptSubspt a b) (h2 : sptSubspt b c) : sptSubspt a c := by
  intro k member
  obtain ⟨mid, e1⟩ := h1 k member
  obtain ⟨last, e2⟩ := h2 k mid
  exact ⟨last, e2.trans e1⟩

/-- Handler case of the original optimizer simulation, with its source body
and raised-exception handler induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0Handle {C F : Type} (trace : BackendCommon.Tra) (body handler : ClosLang.Exp)
    (env1full : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F)
    (handlerIH : ∀ (bodyResult : Result (List ClosSem.Value) ClosSem.Value)
      (middle : State (Spt ValApprox × C) F) (err : ErrorResult ClosSem.Value) (value : ClosSem.Value),
      evaluate [body] env1full s0 = (bodyResult, middle) ∧ bodyResult = .err err ∧ err = .raise value →
      KnownSimulationAt [handler] (value :: env1full) middle)
    (bodyIH : KnownSimulationAt [body] env1full s0) :
    KnownSimulationAt [.handle trace body handler] env1full s0 := by
  intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
  obtain ⟨run, known, state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
    exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
    sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
  have uniqueBoth : uniqueSetGlobals ([body] ++ [handler]) s0.compileOracle := by
    intro n i
    have bound := unique n i
    simp only [elistGlobals_append, elistGlobals, setGlobals,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag] at bound ⊢
    omega
  have ⟨bodyUnique, handlerUnique, swappedUnique⟩ := CorrectApprox.Cons.uniqueParts [body] [handler] s0.compileOracle uniqueBoth
  have ⟨bodyDisjoint, handlerDisjoint⟩ :=
    (mglobalsDisjointRw s0.globals body handler body handler body [] trace .install [] none none [] 0 0).2.2.1.mp disjoint
  have syntaxParts : everyFnVarsNone [body] ∧ everyFnVarsNone [handler] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
  have safeParts := exprSafe (.handle trace body handler) (by simp)
  simp only [esgcFree] at safeParts
  have bodySafe : ∀ e ∈ [body], esgcFree e := by simpa using safeParts.1
  have handlerSafe : ∀ e ∈ [handler], esgcFree e := by simpa using safeParts.2
  have ⟨bodyFree, handlerFree⟩ := (fvMaxHandle env1.length trace body handler).1 free
  have bagDisjoint : ∀ i, elistGlobals [body] i = 0 ∨ elistGlobals [handler] i = 0 := by
    intro i
    have bound := uniqueBoth 0 i
    simp only [elistGlobals_append] at bound
    omega
  cases hk : knownListTotal c [body] aenv g0 with
  | mk bodyEas g1 =>
    obtain ⟨be, ba, eq⟩ := knownListTotal_single_result c body aenv g0 g1 bodyEas hk
    subst bodyEas
    cases hh : knownListTotal c [handler] (.other :: aenv) g1 with
    | mk handlerEas g2 =>
      obtain ⟨he, ha, eq⟩ := knownListTotal_single_result c handler (.other :: aenv) g1 g2 handlerEas hh
      subst handlerEas
      rw [knownListTotal_handle, hk] at known
      dsimp only at known
      rw [hh] at known
      simp [knownSourceHead] at known
      rcases known with ⟨rfl, rfl⟩
      have ⟨subBody, subHandler⟩ := subsptKnownElistGlobals c [body] aenv g0 [(be, ba)] g1
        [handler] (.other :: aenv) [(he, ha)] g2 ⟨hk, hh, sub0, bagDisjoint⟩
      have subBodyNext : sptSubspt g1 (nextG s0) := subsptTrans _ _ _ subHandler sub1
      cases hr : evaluate [body] env1full s0 with
      | mk bodyResult middle =>
        rw [evaluate, fixClock_evaluate, hr] at run
        have bodyNoType : bodyResult ≠ .err (.abort .typeError) := by
          intro eq
          subst bodyResult
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact noType rfl
        have bodyStep := bodyIH bodyResult middle env1 xenv1 env2 xenv2 t0 c g0 g1 aenv [(be, ba)]
          ⟨hr, hk, state, syntaxParts.1, coSyntax, bodyDisjoint, oracle, stateOracleDisjoint,
            bodySafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
            subBody, subBodyNext, mono, bodyFree, envRel, bodyUnique, stateOracle, envEq, bodyNoType⟩
        obtain ⟨targetBodyResult, targetMiddle, targetBodyRun, bodyRel, midState, midGlobals, midStateOracle, midOracle⟩ := bodyStep
        have targetBodyRun' : evaluate [be] (env2 ++ xenv2) t0 = (targetBodyResult, targetMiddle) := by
          simpa using targetBodyRun
        cases bodyResult with
        | val values =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          cases targetBodyResult with
          | err error => simp [resultRel] at bodyRel
          | val targetValues =>
            refine ⟨.val targetValues, targetMiddle, ?_, bodyRel, midState, midGlobals, midStateOracle, midOracle⟩
            simp only [List.map_cons, List.map_nil]
            rw [evaluate, fixClock_evaluate, targetBodyRun']
        | err error =>
          cases error with
          | abort abort =>
            simp at run
            rcases run with ⟨rfl, rfl⟩
            cases targetBodyResult with
            | val values => simp [resultRel] at bodyRel
            | err targetError =>
              cases targetError with
              | raise value => simp [resultRel, excRel] at bodyRel
              | abort targetAbort =>
                refine ⟨.err (.abort targetAbort), targetMiddle, ?_, bodyRel, midState, midGlobals, midStateOracle, midOracle⟩
                simp only [List.map_cons, List.map_nil]
                rw [evaluate, fixClock_evaluate, targetBodyRun']
          | raise value =>
            cases targetBodyResult with
            | val values => simp [resultRel] at bodyRel
            | err targetError =>
              cases targetError with
              | abort targetAbort => simp [resultRel, excRel] at bodyRel
              | raise targetValue =>
                have valueRel : ValueRel c (nextG middle) value targetValue := bodyRel
                have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals [body] env1full s0 (.err (.raise value)) middle
                  ⟨hr, safe, bodySafe, envSafe⟩
                have valueSafe : vsgcFree value := by simpa [rsgcFree] using safety.2.1
                have nextUnique := uniqueSetGlobalsEvaluate [body] [handler] env1full s0 middle (.err (.raise value)) ⟨handlerUnique, hr⟩
                have nextDisjoint := mglobalsDisjointEvaluate s0 [handler] [body] env1full (.err (.raise value)) middle
                  ⟨hr, safe, envSafe, bodySafe, swappedUnique, handlerDisjoint⟩
                have nextStateOracleDisjoint := stateOracleMglobalsDisjointEvaluate [body] env1full s0 (.err (.raise value)) middle
                  ⟨hr, safe, bodySafe, envSafe, bodyUnique, bodyDisjoint, stateOracleDisjoint⟩
                obtain ⟨n, shifted⟩ := evaluateImpShiftSeq [body] env1full s0 (.err (.raise value)) middle hr
                have nextCoSyntax : coEveryFnVarsNone middle.compileOracle := by
                  rw [shifted]
                  exact coEveryFnVarsNoneShift s0.compileOracle coSyntax n
                have nextOracleSafe : oracleStateSgcFree middle.compileOracle := by
                  rw [shifted]
                  exact oracleStateSgcFreeShift s0.compileOracle oracleSafe n
                have nextMono : oracleGapproxSubspt middle.compileOracle :=
                  oracleGapproxSubsptEvaluate () [body] env1full s0 (.err (.raise value)) middle ⟨mono, hr⟩
                have nextTree := nextGEvaluateSubspt [body] env1full s0 (.err (.raise value)) middle ⟨mono, hr⟩
                have nextRel := valueRelListSubspt c (nextG s0) env1 env2 envRel (nextG middle) nextTree
                have nextSafe := (PreserveSafety.knownPreservesEsgcFree c [body] aenv g0 [(be, ba)] g1
                  ⟨hk, bodySafe, approxSafe, globalSafe⟩).2.2
                cases handlerRun : evaluate [handler] (value :: env1full) middle with
                | mk handlerResult last =>
                  have handlerNoType : handlerResult ≠ .err (.abort .typeError) := by
                    intro eq
                    subst handlerResult
                    simp [handlerRun] at run
                    rcases run with ⟨rfl, rfl⟩
                    exact noType rfl
                  have extendedSafe : ∀ v ∈ value :: env1full, vsgcFree v := by
                    simpa using And.intro valueSafe envSafe
                  have extendedApproxSafe : ∀ a ∈ ValApprox.other :: aenv, valApproxSgcFree a := by
                    simpa [valApproxSgcFree] using approxSafe
                  have handlerStep := handlerIH (.err (.raise value)) middle (.raise value) value ⟨hr, rfl, rfl⟩
                    handlerResult last (value :: env1) xenv1 (targetValue :: env2) xenv2 targetMiddle c g1 g2
                    (.other :: aenv) [(he, ha)]
                    ⟨handlerRun, hh, midState, syntaxParts.2, nextCoSyntax, nextDisjoint, midOracle, nextStateOracleDisjoint,
                      handlerSafe, safety.1, extendedSafe, .cons (.other value) approxRel, nextOracleSafe, nextSafe,
                      extendedApproxSafe, midGlobals, subHandler, subsptTrans _ _ _ sub1 nextTree, nextMono,
                      by simpa [Nat.add_comm] using handlerFree, .cons valueRel nextRel, nextUnique, midStateOracle,
                      by simp [envEq], handlerNoType⟩
                  obtain ⟨targetHandlerResult, targetLast, targetHandlerRun, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := handlerStep
                  simp only [handlerRun] at run
                  cases handlerResult <;> cases run <;>
                    refine ⟨targetHandlerResult, targetLast, ?_, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ <;>
                    simp only [List.map_cons, List.map_nil] <;>
                    rw [evaluate, fixClock_evaluate, targetBodyRun'] <;>
                    simpa using targetHandlerRun

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Handle
