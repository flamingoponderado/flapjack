module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.InlineClosureRelation
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.InlineLetEvaluation

@[expose] public section


/-! Inlining branch of known-function application simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.AppInline
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint SubsptComposition
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

private theorem subsptTrans {A : Type} (a b c : Spt A)
    (h1 : sptSubspt a b) (h2 : sptSubspt b c) : sptSubspt a c := by
  intro k member
  obtain ⟨mid, e1⟩ := h1 k member
  obtain ⟨last, e2⟩ := h2 k mid
  exact ⟨last, e2.trans e1⟩

/-- Simulation of an application selected for inlining, including failures in
argument and function evaluation. The decision premise makes this a Flapjack
case helper, not the full HOL induction case. -/
theorem inlineApplicationSimulation {C F : Type} (trace : BackendCommon.Tra)
    (loc : Option Nat) (x first : ClosLang.Exp) (rest : List ClosLang.Exp)
    (env1full env1 xenv1 env2 xenv2 : List ClosSem.Value)
    (s0 final : State (Spt ValApprox × C) F) (t0 : State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value) (c : Config) (aenv : List ValApprox)
    (g0 g1 g2 : Spt ValApprox) (argsEas : List (ClosLang.Exp × ValApprox))
    (fnExp : ClosLang.Exp) (fnApprox : ValApprox)
    (body targetBody : ClosLang.Exp) (bodyApprox : ValApprox) (after : Spt ValApprox)
    (argsIH : KnownSimulationAt (first :: rest) env1full s0)
    (fnIH : ∀ middle values, evaluate (first :: rest) env1full s0 = (.val values, middle) →
      KnownSimulationAt [x] env1full middle)
    (appIH : ∀ middle values next fn, evaluate (first :: rest) env1full s0 = (.val values, middle) →
      evaluate [x] env1full middle = (.val [fn], next) → KnownAppSimulationAt loc fn values next)
    (argsKnown : knownListTotal c (first :: rest) aenv g0 = (argsEas, g1))
    (fnKnown : knownListTotal c [x] aenv g1 = ([(fnExp, fnApprox)], g2))
    (decision : decideInlineHOL c fnApprox loc (first :: rest).length = .letInline body)
    (bodyKnown : knownListTotal (decInlineFactor c) [body] (argsEas.map Prod.snd) g2 =
      ([(targetBody, bodyApprox)], after))
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
      evaluate [.let (BackendCommon.mkCons trace 0)
        (if ClosLang.pure x then argsEas.map Prod.fst else argsEas.map Prod.fst ++ [fnExp])
        (ticks trace 1 (first :: rest).length targetBody)] (env2 ++ xenv2) t0 =
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
  have subArgsNext := subsptTrans g1 g2 (nextG s0) subFn sub1
  have argsOptimizer := PreserveSafety.knownPreservesEsgcFree c (first :: rest) aenv g0 argsEas g1
    ⟨argsKnown, safeParts.2, approxSafe, globalSafe⟩
  have fnSafe : ∀ e ∈ [x], esgcFree e := by simpa using safeParts.1
  have fnOptimizer := PreserveSafety.knownPreservesEsgcFree c [x] aenv g1 [(fnExp, fnApprox)] g2
    ⟨fnKnown, fnSafe, approxSafe, argsOptimizer.2.2⟩
  have fnApproxSafe : valApproxSgcFree fnApprox := by simpa using fnOptimizer.2.1
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
        refine ⟨.err targetError, targetFinal, ?_, resultRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩
        exact InlineLetEvaluation.inlineLetArgsError (BackendCommon.mkCons trace 0) (ClosLang.pure x)
          (argsEas.map Prod.fst) fnExp (ticks trace 1 (first :: rest).length targetBody)
          (env2 ++ xenv2) t0 targetFinal targetError targetRun
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
          argsRel, valuesApprox, fnRel, fnSound, nextSafe, fnSafe, valuesSafe, nextOracleSafe, nextCoSyntax,
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
            have impure : ClosLang.pure x = false := by
              cases hp : ClosLang.pure x with
              | false => rfl
              | true =>
                have sourcePure : ClosLang.pureList [x] = true := by simpa [ClosLang.pureList] using hp
                obtain ⟨_, impossible, _⟩ := evaluate_pure [x] env1full middle next (.err error)
                  sourcePure fnRun fnNoType
                cases impossible
            refine ⟨.err targetError, targetNext, ?_, fnRel, nextState, nextGlobals, nextStateOracle, nextOracle⟩
            simpa [impure] using InlineLetEvaluation.inlineLetFunctionError
              (BackendCommon.mkCons trace 0) (argsEas.map Prod.fst) fnExp
              (ticks trace 1 (first :: rest).length targetBody) (env2 ++ xenv2) targetValues
              t0 targetMiddle targetNext targetError targetArgsRun targetFnRun
        | val fnValues =>
          obtain ⟨fn, rfl⟩ := evaluate_singleton_value x env1full middle next fnValues fnRun
          cases targetFnResult with
          | err error => simp [resultRel] at fnRel
          | val targetFns =>
            cases fnRel with
            | cons fnRelated relatedTail =>
              cases relatedTail
              have sound := fnSound [fn] rfl
              cases sound with
              | cons fnSound _ =>
                have fnValueSafe : vsgcFree fn := by simpa [rsgcFree] using fnSafe
                have lengthEq := evaluate_length.1 (first :: rest) env1full s0 middle values argsRun
                have valuesNonempty : values ≠ [] := by
                  intro eq
                  simp [eq] at lengthEq
                have tree1 := nextGEvaluateSubspt (first :: rest) env1full s0 (.val values) middle ⟨mono, argsRun⟩
                have mono1 := oracleGapproxSubsptEvaluate () (first :: rest) env1full s0 (.val values) middle ⟨mono, argsRun⟩
                have tree2 := nextGEvaluateSubspt [x] env1full middle (.val [fn]) next ⟨mono1, fnRun⟩
                have subNext := subsptTrans g2 (nextG s0) (nextG next) sub1
                  (subsptTrans (nextG s0) (nextG middle) (nextG next) tree1 tree2)
                have targetUnchanged : ClosLang.pure x = true → targetNext = targetMiddle := by
                  intro hp
                  obtain ⟨_, _, _, _, _, targetEq, _⟩ := InlinePureEvaluation.pureFunctionEvaluation
                    c x fnExp env1full (env2 ++ xenv2) aenv g1 g2 (nextG next) fnApprox
                    middle next targetMiddle targetNext (.val [fn]) (.val [_]) fnKnown hp fnRun targetFnRun
                    (by simpa [resultRel] using List.Forall₂.cons fnRelated List.Forall₂.nil) (by simp)
                  exact targetEq
                cases appRun : evaluateApp loc fn values next with
                | mk appResult last =>
                  simp [evaluate, argsRun, fixArgs, fnRun, fixFn, appRun] at run
                  rcases run with ⟨rfl, rfl⟩
                  obtain ⟨targetResult, targetFinal, targetBodyRun, resultRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩ :=
                    InlineClosureRelation.inlineApplicationContinuation c trace loc (first :: rest).length
                      fnApprox body targetBody bodyApprox g2 after (argsEas.map Prod.snd) fn _ values targetValues
                      (if ClosLang.pure x then env2 ++ xenv2 else _ :: (env2 ++ xenv2)) next targetNext appResult last
                      (appIH middle values next fn argsRun fnRun) decision fnSound valuesApprox argsOptimizer.2.1
                      fnApproxSafe fnOptimizer.2.2 bodyKnown subNext lengthEq.symm valuesNonempty
                      ⟨argsRel, fnRelated, nextSafe, fnValueSafe, valuesSafe, nextOracleSafe, nextCoSyntax,
                        nextUnique, nextDisjoint, nextMono, nextState, nextGlobals, nextStateOracle, nextOracle⟩ appRun noType
                  refine ⟨targetResult, targetFinal, ?_, resultRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩
                  exact InlineLetEvaluation.inlineLetSuccess (BackendCommon.mkCons trace 0) (ClosLang.pure x)
                    (argsEas.map Prod.fst) fnExp (ticks trace 1 (first :: rest).length targetBody)
                    (env2 ++ xenv2) targetValues _ t0 targetMiddle targetNext targetFinal targetResult
                    targetArgsRun targetFnRun targetUnchanged targetBodyRun

end Flapjack.Compiler.Backend.ClosKnown.Simulation.AppInline
