module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationCons
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationBool
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBoolean

@[expose] public section


/-! Conditional case of the known-function semantic simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.If
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint SubsptComposition
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Conditional case of the original optimizer simulation, retaining the
source evaluator's condition and branch induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0If {C F : Type} (trace : BackendCommon.Tra) (cond yes no : ClosLang.Exp)
    (env1full : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F)
    (noIH : ∀ (condResult : Result (List ClosSem.Value) ClosSem.Value)
      (middle : State (Spt ValApprox × C) F) (values : List ClosSem.Value),
      evaluate [cond] env1full s0 = (condResult, middle) ∧ condResult = .val values ∧
      ClosSem.boolValue true ≠ @Flapjack.holHd ClosSem.Value ⟨unitValue⟩ values ∧
      ClosSem.boolValue false = @Flapjack.holHd ClosSem.Value ⟨unitValue⟩ values →
      KnownSimulationAt [no] env1full middle)
    (yesIH : ∀ (condResult : Result (List ClosSem.Value) ClosSem.Value)
      (middle : State (Spt ValApprox × C) F) (values : List ClosSem.Value),
      evaluate [cond] env1full s0 = (condResult, middle) ∧ condResult = .val values ∧
      ClosSem.boolValue true = @Flapjack.holHd ClosSem.Value ⟨unitValue⟩ values →
      KnownSimulationAt [yes] env1full middle)
    (condIH : KnownSimulationAt [cond] env1full s0) :
    KnownSimulationAt [.ifThenElse trace cond yes no] env1full s0 := by
  intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
  obtain ⟨run, known, state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
    exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
    sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
  have uniqueAll : uniqueSetGlobals ([cond] ++ ([yes] ++ [no])) s0.compileOracle := by
    intro n i
    have bound := unique n i
    simp only [elistGlobals_append, elistGlobals, setGlobals, FlatProps.unionGlobalBag,
      FlatProps.emptyGlobalBag, Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag] at bound ⊢
    omega
  have ⟨condUnique, branchesUnique, swappedUnique⟩ := CorrectApprox.Cons.uniqueParts [cond] ([yes] ++ [no]) s0.compileOracle uniqueAll
  have ⟨condDisjoint, yesDisjoint, noDisjoint⟩ :=
    (mglobalsDisjointRw s0.globals cond yes cond yes no [] trace .install [] none none [] 0 0).2.2.2.1.mp disjoint
  have branchesDisjoint : mglobalsDisjoint s0.globals ([yes] ++ [no]) :=
    (mglobalsDisjointRw s0.globals yes no yes yes yes [] trace .install [] none none [] 0 0).1.mpr
      ⟨yesDisjoint, noDisjoint⟩
  have syntaxParts : everyFnVarsNone [cond] ∧ everyFnVarsNone [yes] ∧ everyFnVarsNone [no] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
  have allSafe := exprSafe (.ifThenElse trace cond yes no) (by simp)
  simp only [esgcFree] at allSafe
  have condSafe : ∀ e ∈ [cond], esgcFree e := by simpa using allSafe.1
  have yesSafe : ∀ e ∈ [yes], esgcFree e := by simpa using allSafe.2.1
  have noSafe : ∀ e ∈ [no], esgcFree e := by simpa using allSafe.2.2
  have freeParts : fvMax env1.length [cond] ∧ fvMax env1.length [yes] ∧ fvMax env1.length [no] := by
    simpa [fvMax, freeVars, freeVarExp, or_imp, forall_and] using free
  have condDisjointBags : ∀ i, elistGlobals [cond] i = 0 ∨ elistGlobals ([yes] ++ [no]) i = 0 := by
    intro i
    have bound := uniqueAll 0 i
    simp only [elistGlobals_append] at bound ⊢
    omega
  have yesNoDisjointBags : ∀ i, elistGlobals [yes] i = 0 ∨ elistGlobals [no] i = 0 := by
    intro i
    have bound := branchesUnique 0 i
    simp only [elistGlobals_append] at bound
    omega
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
        have ⟨subCond, subBranches⟩ := subsptKnownElistGlobals c [cond] aenv g0 [(ec, ac)] g1
          ([yes] ++ [no]) aenv [(ey, ay), (en, an)] g3 ⟨hc, branchesKnown, sub0, condDisjointBags⟩
        have ⟨subYes, subNo⟩ := subsptKnownElistGlobals c [yes] aenv g1 [(ey, ay)] g2
          [no] aenv [(en, an)] g3 ⟨hy, hn, subBranches, yesNoDisjointBags⟩
        have subCondNext : sptSubspt g1 (nextG s0) := sptSubsptTrans _ _ _ ⟨subBranches, sub1⟩
        cases hr : evaluate [cond] env1full s0 with
        | mk condResult middle =>
          rw [evaluate, fixClock_evaluate, hr] at run
          have condNoType : condResult ≠ .err (.abort .typeError) := by
            intro eq
            subst condResult
            simp at run
            rcases run with ⟨rfl, rfl⟩
            exact noType rfl
          have condStep := condIH condResult middle env1 xenv1 env2 xenv2 t0 c g0 g1 aenv [(ec, ac)]
            ⟨hr, hc, state, syntaxParts.1, coSyntax, condDisjoint, oracle, stateOracleDisjoint,
              condSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
              subCond, subCondNext, mono, freeParts.1, envRel, condUnique, stateOracle, envEq, condNoType⟩
          obtain ⟨targetCondResult, targetMiddle, targetCondRun, condRel, midState, midGlobals, midStateOracle, midOracle⟩ := condStep
          have targetCondRun' : evaluate [ec] (env2 ++ xenv2) t0 = (targetCondResult, targetMiddle) := by simpa using targetCondRun
          cases condResult with
          | err error =>
            simp at run
            rcases run with ⟨rfl, rfl⟩
            cases targetCondResult with
            | val values => simp [resultRel] at condRel
            | err error2 =>
              refine ⟨.err error2, targetMiddle, ?_, condRel, midState, midGlobals, midStateOracle, midOracle⟩
              simp only [List.map_cons, List.map_nil]
              rw [evaluate, fixClock_evaluate, targetCondRun']
          | val values =>
            obtain ⟨value, rfl⟩ := evaluate_singleton_value cond env1full s0 middle values hr
            cases targetCondResult with
            | err error => simp [resultRel] at condRel
            | val targetValues =>
              obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value ec (env2 ++ xenv2) t0 targetMiddle targetValues targetCondRun'
              have valRel : ValueRel c (nextG middle) value targetValue := by cases condRel with | cons rel _ => exact rel
              have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals [cond] env1full s0 (.val [value]) middle
                ⟨hr, safe, condSafe, envSafe⟩
              have middleUnique := uniqueSetGlobalsEvaluate [cond] ([yes] ++ [no]) env1full s0 middle
                (.val [value]) ⟨branchesUnique, hr⟩
              have ⟨yesUnique, noUnique, _⟩ := CorrectApprox.Cons.uniqueParts [yes] [no] middle.compileOracle middleUnique
              have middleDisjoint := mglobalsDisjointEvaluate s0 ([yes] ++ [no]) [cond] env1full
                (.val [value]) middle ⟨hr, safe, envSafe, condSafe, swappedUnique, branchesDisjoint⟩
              have ⟨yesDisjoint', noDisjoint'⟩ :=
                (mglobalsDisjointRw middle.globals yes no yes yes yes [] trace .install [] none none [] 0 0).1.mp middleDisjoint
              have nextStateOracleDisjoint := stateOracleMglobalsDisjointEvaluate [cond] env1full s0 (.val [value]) middle
                ⟨hr, safe, condSafe, envSafe, condUnique, condDisjoint, stateOracleDisjoint⟩
              obtain ⟨n, shifted⟩ := evaluateImpShiftSeq [cond] env1full s0 (.val [value]) middle hr
              have nextCoSyntax : coEveryFnVarsNone middle.compileOracle := by
                rw [shifted]; exact coEveryFnVarsNoneShift s0.compileOracle coSyntax n
              have nextOracleSafe : oracleStateSgcFree middle.compileOracle := by
                rw [shifted]; exact oracleStateSgcFreeShift s0.compileOracle oracleSafe n
              have nextMono : oracleGapproxSubspt middle.compileOracle :=
                oracleGapproxSubsptEvaluate () [cond] env1full s0 (.val [value]) middle ⟨mono, hr⟩
              have nextTree := nextGEvaluateSubspt [cond] env1full s0 (.val [value]) middle ⟨mono, hr⟩
              have nextRel := valueRelListSubspt c (nextG s0) env1 env2 envRel (nextG middle) nextTree
              have nextSafe := (PreserveSafety.knownPreservesEsgcFree c [cond] aenv g0 [(ec, ac)] g1
                ⟨hc, condSafe, approxSafe, globalSafe⟩).2.2
              change (match asBool value with
                | none => (.err (.abort .typeError), middle)
                | some true => evaluate [yes] env1full middle
                | some false => evaluate [no] env1full middle) = (res1, s) at run
              cases decoded : asBool value with
              | none =>
                simp [decoded] at run
                rcases run with ⟨rfl, rfl⟩
                exact False.elim (noType rfl)
              | some flag =>
                have valueEq := (asBool_eq_some value flag).1 decoded
                subst value
                have targetEq : targetValue = ClosSem.boolValue flag := (valueRelBool c (nextG middle) flag targetValue).1.mp valRel
                subst targetValue
                cases flag with
                | true =>
                  simp only [decoded] at run
                  cases yesRun : evaluate [yes] env1full middle with
                  | mk yesResult last =>
                    have yesNoType : yesResult ≠ .err (.abort .typeError) := by
                      intro eq; subst yesResult; rw [yesRun] at run; cases run; exact noType rfl
                    have yesStep := yesIH (.val [ClosSem.boolValue true]) middle [ClosSem.boolValue true] ⟨hr, rfl, by simp [Flapjack.holHd]⟩
                      yesResult last env1 xenv1 env2 xenv2 targetMiddle c g1 g2 aenv [(ey, ay)]
                      ⟨yesRun, hy, midState, syntaxParts.2.1, nextCoSyntax, yesDisjoint', midOracle, nextStateOracleDisjoint,
                        yesSafe, safety.1, envSafe, approxRel, nextOracleSafe, nextSafe, approxSafe, midGlobals,
                        subYes, sptSubsptTrans _ _ _ ⟨sptSubsptTrans _ _ _ ⟨subNo, sub1⟩, nextTree⟩, nextMono, freeParts.2.1,
                        nextRel, yesUnique, midStateOracle, envEq, yesNoType⟩
                    obtain ⟨res2, targetLast, targetRun, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := yesStep
                    rw [yesRun] at run
                    cases yesResult <;> cases run <;>
                      refine ⟨res2, targetLast, ?_, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ <;>
                      simp only [List.map_cons, List.map_nil] <;>
                      rw [evaluate, fixClock_evaluate, targetCondRun'] <;>
                      simpa [asBool, ClosSem.boolValue, BackendCommon.trueTag] using targetRun
                | false =>
                  simp only [decoded] at run
                  have g2Safe := (PreserveSafety.knownPreservesEsgcFree c [yes] aenv g1 [(ey, ay)] g2
                    ⟨hy, yesSafe, approxSafe, nextSafe⟩).2.2
                  cases noRun : evaluate [no] env1full middle with
                  | mk noResult last =>
                    have noNoType : noResult ≠ .err (.abort .typeError) := by
                      intro eq; subst noResult; rw [noRun] at run; cases run; exact noType rfl
                    have noStep := noIH (.val [ClosSem.boolValue false]) middle [ClosSem.boolValue false]
                      ⟨hr, rfl, by simp [Flapjack.holHd, ClosSem.boolValue, BackendCommon.trueTag, BackendCommon.falseTag], by simp [Flapjack.holHd]⟩
                      noResult last env1 xenv1 env2 xenv2 targetMiddle c g2 g3 aenv [(en, an)]
                      ⟨noRun, hn, midState, syntaxParts.2.2, nextCoSyntax, noDisjoint', midOracle, nextStateOracleDisjoint,
                        noSafe, safety.1, envSafe, approxRel, nextOracleSafe, g2Safe, approxSafe, midGlobals,
                        subNo, sptSubsptTrans _ _ _ ⟨sub1, nextTree⟩, nextMono, freeParts.2.2,
                        nextRel, noUnique, midStateOracle, envEq, noNoType⟩
                    obtain ⟨res2, targetLast, targetRun, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := noStep
                    rw [noRun] at run
                    cases noResult <;> cases run <;>
                      refine ⟨res2, targetLast, ?_, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ <;>
                      simp only [List.map_cons, List.map_nil] <;>
                      rw [evaluate, fixClock_evaluate, targetCondRun'] <;>
                      simpa [asBool, ClosSem.boolValue, BackendCommon.falseTag] using targetRun

end Flapjack.Compiler.Backend.ClosKnown.Simulation.If
