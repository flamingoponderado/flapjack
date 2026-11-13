module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationAppPrefix
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationApplyPartial

@[expose] public section


/-! Unchanged and annotated application branches of known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.AppNonInline
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint SubsptComposition
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- Simulation of an application when the optimizer leaves the call in place,
including errors in either preliminary evaluation. The decision premise makes
this a Flapjack case helper, not the full HOL induction case. -/
theorem nonInlineApplicationSimulation {C F : Type} (trace : BackendCommon.Tra)
    (loc targetLoc : Option Nat) (x first : ClosLang.Exp) (rest : List ClosLang.Exp)
    (env1full env1 xenv1 env2 xenv2 : List ClosSem.Value)
    (s0 final : State (Spt ValApprox × C) F) (t0 : State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value) (c : Config) (aenv : List ValApprox)
    (g0 g1 g2 : Spt ValApprox) (argsEas : List (ClosLang.Exp × ValApprox))
    (fnExp : ClosLang.Exp) (fnApprox : ValApprox)
    (argsIH : KnownSimulationAt (first :: rest) env1full s0)
    (fnIH : ∀ middle values, evaluate (first :: rest) env1full s0 = (.val values, middle) →
      KnownSimulationAt [x] env1full middle)
    (appIH : ∀ middle values next fn, evaluate (first :: rest) env1full s0 = (.val values, middle) →
      evaluate [x] env1full middle = (.val [fn], next) → KnownAppSimulationAt loc fn values next)
    (argsKnown : knownListTotal c (first :: rest) aenv g0 = (argsEas, g1))
    (fnKnown : knownListTotal c [x] aenv g1 = ([(fnExp, fnApprox)], g2))
    (choice : targetLoc = loc ∨ ∃ address, targetLoc = some address ∧
      decideInlineHOL c fnApprox loc (first :: rest).length = .annotate address)
    (run : evaluate [.app trace loc x (first :: rest)] env1full s0 = (result, final))
    (noType : result ≠ .err (.abort .typeError))
    (h : StateRel c (nextG s0) s0 t0 ∧ everyFnVarsNone [.app trace loc x (first :: rest)] ∧
      coEveryFnVarsNone s0.compileOracle ∧ mglobalsDisjoint s0.globals [.app trace loc x (first :: rest)] ∧
      oracleGapproxDisjoint (nextG s0) s0.compileOracle ∧ stateOracleMglobalsDisjoint s0 ∧
      (∀ e ∈ [ClosLang.Exp.app trace loc x (first :: rest)], esgcFree e) ∧ ssgcFree s0 ∧
      (∀ v ∈ env1full, vsgcFree v) ∧ List.Forall₂ ValApproxVal aenv env1 ∧
      oracleStateSgcFree s0.compileOracle ∧ globalsApproxSgcFree g0 ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ stateGlobalsApprox s0 (nextG s0) ∧
      sptSubspt g0 g2 ∧ sptSubspt g2 (nextG s0) ∧ oracleGapproxSubspt s0.compileOracle ∧
      fvMax env1.length [.app trace loc x (first :: rest)] ∧
      List.Forall₂ (ValueRel c (nextG s0)) env1 env2 ∧
      uniqueSetGlobals [.app trace loc x (first :: rest)] s0.compileOracle ∧
      isStateOracle (compileInc c) s0.compileOracle ∧ env1full = env1 ++ xenv1) :
    ∃ targetResult targetFinal,
      evaluate [.app trace targetLoc fnExp (argsEas.map Prod.fst)] (env2 ++ xenv2) t0 =
        (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG final))) (ValueRel c (nextG final)) result targetResult ∧
      StateRel c (nextG final) final targetFinal ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧
      oracleGapproxDisjoint (nextG final) final.compileOracle := by
  have hPrefix := h
  obtain ⟨state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
    exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
    sub0, sub1, mono, free, envRel, unique, stateOracle, envEq⟩ := h
  have uniqueBoth : uniqueSetGlobals ((first :: rest) ++ [x]) s0.compileOracle := by
    intro n i
    have bound := unique n i
    simp only [elistGlobals_append, elistGlobals, setGlobals,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag] at bound ⊢
    omega
  have ⟨argsUnique, _, _⟩ := CorrectApprox.Cons.uniqueParts (first :: rest) [x] s0.compileOracle uniqueBoth
  have ⟨_, argsDisjoint⟩ :=
    (mglobalsDisjointRw s0.globals x x x x x (first :: rest) trace .install [] loc none [] 0 0).2.2.2.2.2.2.2.2.1.mp disjoint
  have argsSyntax : everyFnVarsNone (first :: rest) := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using (show everyFnVarsNone [x] ∧ everyFnVarsNone (first :: rest) by
      simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax).2
  have safeParts := exprSafe (.app trace loc x (first :: rest)) (by simp)
  simp only [esgcFree, esgcFreeList_iff] at safeParts
  have argsFree : fvMax env1.length (first :: rest) := by
    have parts : fvMax env1.length [x] ∧ fvMax env1.length (first :: rest) := by
      simpa [fvMax, freeVars, freeVarExp, or_imp, forall_and] using free
    exact parts.2
  have bagDisjoint : ∀ i, elistGlobals (first :: rest) i = 0 ∨ elistGlobals [x] i = 0 := by
    intro i
    have bound := uniqueBoth 0 i
    simp only [elistGlobals_append] at bound
    omega
  have ⟨subArgs, subFn⟩ := subsptKnownElistGlobals c (first :: rest) aenv g0 argsEas g1
    [x] aenv [(fnExp, fnApprox)] g2 ⟨argsKnown, fnKnown, sub0, bagDisjoint⟩
  have subArgsNext := sptSubsptTrans g1 g2 (nextG s0) ⟨subFn, sub1⟩
  have argsLength := knownListTotal_length c (first :: rest) aenv g0
  rw [argsKnown] at argsLength
  have argsNonempty : argsEas.map Prod.fst ≠ [] := by
    intro empty
    have len : (argsEas.map Prod.fst).length = 0 := by rw [empty]; rfl
    simp only [List.length_map] at len
    simp only [List.length_cons] at argsLength
    omega
  have argsEasNonempty : argsEas ≠ [] := by
    intro eq
    subst argsEas
    exact argsNonempty rfl
  cases argsRun : evaluate (first :: rest) env1full s0 with
  | mk argsResult middle =>
    have fixArgs : fixClock s0 (argsResult, middle) = (argsResult, middle) := by
      simpa only [argsRun] using fixClock_evaluate (first :: rest) env1full s0
    have argsNoType : argsResult ≠ .err (.abort .typeError) := by
      intro eq
      subst argsResult
      simp [evaluate, argsRun, fixArgs] at run
      rcases run with ⟨rfl, rfl⟩
      exact noType rfl
    cases argsResult with
    | err error =>
      have argsStep := argsIH (.err error) middle env1 xenv1 env2 xenv2 t0 c g0 g1 aenv argsEas
        ⟨argsRun, argsKnown, state, argsSyntax, coSyntax, argsDisjoint, oracle, stateOracleDisjoint,
          safeParts.2, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
          subArgs, subArgsNext, mono, argsFree, envRel, argsUnique, stateOracle, envEq, argsNoType⟩
      obtain ⟨targetResult, targetFinal, targetRun, resultRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := argsStep
      simp [evaluate, argsRun, fixArgs] at run
      rcases run with ⟨rfl, rfl⟩
      cases targetResult with
      | val vals => simp [Flapjack.SemanticPrimitivesProps.resultRel] at resultRel
      | err targetError =>
        have targetFix := fixClock_evaluate (argsEas.map Prod.fst) (env2 ++ xenv2) t0
        rw [targetRun] at targetFix
        refine ⟨.err targetError, targetFinal, ?_, resultRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩
        simp [evaluate, argsEasNonempty, targetRun, targetFix]
    | val values =>
      cases fnRun : evaluate [x] env1full middle with
      | mk fnResult next =>
        have fixFn : fixClock middle (fnResult, next) = (fnResult, next) := by
          simpa only [fnRun] using fixClock_evaluate [x] env1full middle
        have fnNoType : fnResult ≠ .err (.abort .typeError) := by
          intro eq
          subst fnResult
          simp [evaluate, argsRun, fixArgs, fnRun, fixFn] at run
          rcases run with ⟨rfl, rfl⟩
          exact noType rfl
        obtain ⟨targetValues, targetFnResult, targetMiddle, targetNext, targetArgsRun, targetFnRun,
          argsRel, _, fnRel, fnSound, nextSafe, fnSafe, valuesSafe, nextOracleSafe, nextCoSyntax,
          nextUnique, nextDisjoint, nextMono, nextState, nextGlobals, nextStateOracle, nextOracle⟩ :=
          AppPrefix.applicationPrefixSimulation trace loc x (first :: rest) env1full env1 xenv1 env2 xenv2
            s0 middle next t0 values fnResult c aenv g0 g1 g2 argsEas fnExp fnApprox argsIH
            (fnIH middle values argsRun) argsRun fnRun fnNoType argsKnown fnKnown hPrefix
        cases fnResult with
        | err error =>
          simp [evaluate, argsRun, fixArgs, fnRun, fixFn] at run
          rcases run with ⟨rfl, rfl⟩
          cases targetFnResult with
          | val vals => simp [resultRel] at fnRel
          | err targetError =>
            have targetArgsFix := fixClock_evaluate (argsEas.map Prod.fst) (env2 ++ xenv2) t0
            rw [targetArgsRun] at targetArgsFix
            have targetFnFix := fixClock_evaluate [fnExp] (env2 ++ xenv2) targetMiddle
            rw [targetFnRun] at targetFnFix
            refine ⟨.err targetError, targetNext, ?_, fnRel, nextState, nextGlobals, nextStateOracle, nextOracle⟩
            simp [evaluate, argsEasNonempty, targetArgsRun, targetArgsFix, targetFnRun, targetFnFix]
        | val fnValues =>
          obtain ⟨fn, rfl⟩ := evaluate_singleton_value x env1full middle next fnValues fnRun
          cases targetFnResult with
          | err error => simp [resultRel] at fnRel
          | val targetFns =>
            cases fnRel with
            | cons fnRelated relatedTail =>
              cases relatedTail
              rename_i targetFn
              have sound := fnSound [fn] rfl
              cases sound with
              | cons fnSound _ =>
                have fnValueSafe : vsgcFree fn := by simpa [rsgcFree] using fnSafe
                have lengthEq := evaluate_length.1 (first :: rest) env1full s0 middle values argsRun
                cases appRun : evaluateApp loc fn values next with
                | mk appResult last =>
                  simp [evaluate, argsRun, fixArgs, fnRun, fixFn, appRun] at run
                  rcases run with ⟨rfl, rfl⟩
                  have locRel : loptRel targetFn values.length loc targetLoc := by
                    rcases choice with equal | ⟨address, rfl, decision⟩
                    · exact Or.inl equal
                    · simpa [lengthEq] using ApplyPartial.annotatedApplicationLocation c (nextG next)
                        fnApprox fn targetFn loc (first :: rest).length address decision fnSound fnRelated
                  obtain ⟨targetResult, targetFinal, targetAppRun, resultRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩ :=
                    (appIH middle values next fn argsRun fnRun) appResult last targetLoc targetFn targetValues targetNext c none
                      ⟨appRun, by simpa [valueRelAppNone] using fnRelated, nextOracle, nextDisjoint,
                        nextSafe, fnValueSafe, valuesSafe, nextOracleSafe, nextCoSyntax, nextUnique,
                        nextStateOracle, argsRel, nextState, nextGlobals, nextMono, locRel, by simp, noType⟩
                  refine ⟨targetResult, targetFinal, ?_, resultRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩
                  have targetArgsFix := fixClock_evaluate (argsEas.map Prod.fst) (env2 ++ xenv2) t0
                  rw [targetArgsRun] at targetArgsFix
                  have targetFnFix := fixClock_evaluate [fnExp] (env2 ++ xenv2) targetMiddle
                  rw [targetFnRun] at targetFnFix
                  simp [evaluate, argsEasNonempty, targetArgsRun, targetArgsFix, targetFnRun, targetFnFix, targetAppRun]

end Flapjack.Compiler.Backend.ClosKnown.Simulation.AppNonInline
