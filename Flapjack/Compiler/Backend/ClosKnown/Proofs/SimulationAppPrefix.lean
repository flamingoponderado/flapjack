import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationLet
import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxApp
import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationApplyPartial

/-! Successful argument and function evaluation in the application case. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.AppPrefix
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

/-- After successful argument evaluation, the source induction hypotheses
simulate the function evaluation, including errors. This Flapjack helper also
preserves the approximation of any resulting runtime function. -/
theorem applicationPrefixSimulation {C F : Type} (trace : BackendCommon.Tra)
    (loc : Option Nat) (x : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env1full env1 xenv1 env2 xenv2 : List ClosSem.Value)
    (s0 middle next : State (Spt ValApprox × C) F) (t0 : State C F)
    (values : List ClosSem.Value) (fnResult : Result (List ClosSem.Value) ClosSem.Value)
    (c : Config) (aenv : List ValApprox)
    (g0 g1 g2 : Spt ValApprox) (argsEas : List (ClosLang.Exp × ValApprox))
    (fnExp : ClosLang.Exp) (fnApprox : ValApprox)
    (argsIH : KnownSimulationAt xs env1full s0)
    (fnIH : KnownSimulationAt [x] env1full middle)
    (argsRun : evaluate xs env1full s0 = (.val values, middle))
    (fnRun : evaluate [x] env1full middle = (fnResult, next))
    (fnNoType : fnResult ≠ .err (.abort .typeError))
    (argsKnown : knownListTotal c xs aenv g0 = (argsEas, g1))
    (fnKnown : knownListTotal c [x] aenv g1 = ([(fnExp, fnApprox)], g2))
    (h : StateRel c (nextG s0) s0 t0 ∧ everyFnVarsNone [.app trace loc x xs] ∧
      coEveryFnVarsNone s0.compileOracle ∧ mglobalsDisjoint s0.globals [.app trace loc x xs] ∧
      oracleGapproxDisjoint (nextG s0) s0.compileOracle ∧ stateOracleMglobalsDisjoint s0 ∧
      (∀ e ∈ [ClosLang.Exp.app trace loc x xs], esgcFree e) ∧ ssgcFree s0 ∧
      (∀ v ∈ env1full, vsgcFree v) ∧ List.Forall₂ ValApproxVal aenv env1 ∧
      oracleStateSgcFree s0.compileOracle ∧ globalsApproxSgcFree g0 ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ stateGlobalsApprox s0 (nextG s0) ∧
      sptSubspt g0 g2 ∧ sptSubspt g2 (nextG s0) ∧ oracleGapproxSubspt s0.compileOracle ∧
      fvMax env1.length [.app trace loc x xs] ∧
      List.Forall₂ (ValueRel c (nextG s0)) env1 env2 ∧
      uniqueSetGlobals [.app trace loc x xs] s0.compileOracle ∧
      isStateOracle (compileInc c) s0.compileOracle ∧ env1full = env1 ++ xenv1) :
    ∃ targetValues targetFnResult targetMiddle targetNext,
      evaluate (argsEas.map Prod.fst) (env2 ++ xenv2) t0 = (.val targetValues, targetMiddle) ∧
      evaluate [fnExp] (env2 ++ xenv2) targetMiddle = (targetFnResult, targetNext) ∧
      List.Forall₂ (ValueRel c (nextG next)) values targetValues ∧
      List.Forall₂ ValApproxVal (argsEas.map Prod.snd) values ∧
      resultRel (List.Forall₂ (ValueRel c (nextG next))) (ValueRel c (nextG next)) fnResult targetFnResult ∧
      (∀ vs, fnResult = .val vs → List.Forall₂ ValApproxVal [fnApprox] vs) ∧
      ssgcFree next ∧ rsgcFree fnResult ∧ (∀ v ∈ values, vsgcFree v) ∧
      oracleStateSgcFree next.compileOracle ∧ coEveryFnVarsNone next.compileOracle ∧
      uniqueSetGlobals [] next.compileOracle ∧ stateOracleMglobalsDisjoint next ∧
      oracleGapproxSubspt next.compileOracle ∧
      StateRel c (nextG next) next targetNext ∧ stateGlobalsApprox next (nextG next) ∧
      isStateOracle (compileInc c) next.compileOracle ∧
      oracleGapproxDisjoint (nextG next) next.compileOracle := by
  obtain ⟨state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
    exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
    sub0, sub1, mono, free, envRel, unique, stateOracle, envEq⟩ := h
  have uniqueBoth : uniqueSetGlobals (xs ++ [x]) s0.compileOracle := by
    intro n i
    have bound := unique n i
    simp only [elistGlobals_append, elistGlobals, setGlobals,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag] at bound ⊢
    omega
  have ⟨argsUnique, fnUnique, swappedUnique⟩ := CorrectApprox.Cons.uniqueParts xs [x] s0.compileOracle uniqueBoth
  have ⟨fnDisjoint, argsDisjoint⟩ :=
    (mglobalsDisjointRw s0.globals x x x x x xs trace .install [] loc none [] 0 0).2.2.2.2.2.2.2.2.1.mp disjoint
  have syntaxParts : everyFnVarsNone [x] ∧ everyFnVarsNone xs := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
  have safeParts := exprSafe (.app trace loc x xs) (by simp)
  simp only [esgcFree, esgcFreeList_iff] at safeParts
  have fnSafe : ∀ e ∈ [x], esgcFree e := by simpa using safeParts.1
  have freeParts : fvMax env1.length [x] ∧ fvMax env1.length xs := by
    simpa [fvMax, freeVars, freeVarExp, or_imp, forall_and] using free
  have bagDisjoint : ∀ i, elistGlobals xs i = 0 ∨ elistGlobals [x] i = 0 := by
    intro i
    have bound := uniqueBoth 0 i
    simp only [elistGlobals_append] at bound
    omega
  have ⟨subArgs, subFn⟩ := subsptKnownElistGlobals c xs aenv g0 argsEas g1
    [x] aenv [(fnExp, fnApprox)] g2 ⟨argsKnown, fnKnown, sub0, bagDisjoint⟩
  have subArgsNext := subsptTrans g1 g2 (nextG s0) subFn sub1
  have startSub := subsptTrans g0 g2 (nextG s0) sub0 sub1
  have startApprox := stateGlobalsApproxSubspt g0 (nextG s0) s0 ⟨startSub, globals⟩
  have startOracle := oracleGapproxDisjointSubspt g0 (nextG s0) s0.compileOracle ⟨startSub, oracle⟩
  have argsApprox := CorrectApprox.Total.knownCorrectApprox c xs aenv g0 argsEas g1 env1 xenv1 s0
    (.val values) middle ⟨argsKnown, by simpa [envEq] using argsRun, argsUnique, approxRel,
      startApprox, argsDisjoint, startOracle, safe, by simpa [← envEq] using envSafe,
      safeParts.2, approxSafe, globalSafe⟩
  have argsStep := argsIH (.val values) middle env1 xenv1 env2 xenv2 t0 c g0 g1 aenv argsEas
    ⟨argsRun, argsKnown, state, syntaxParts.2, coSyntax, argsDisjoint, oracle, stateOracleDisjoint,
      safeParts.2, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
      subArgs, subArgsNext, mono, freeParts.2, envRel, argsUnique, stateOracle, envEq, by simp⟩
  obtain ⟨targetArgsResult, targetMiddle, targetArgsRun, argsRel, midState, midGlobals, midStateOracle, midOracle⟩ := argsStep
  cases targetArgsResult with
  | err error => simp [resultRel] at argsRel
  | val targetValues =>
    have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals xs env1full s0 (.val values) middle
      ⟨argsRun, safe, safeParts.2, envSafe⟩
    have nextUnique := uniqueSetGlobalsEvaluate xs [x] env1full s0 middle (.val values) ⟨fnUnique, argsRun⟩
    have nextDisjoint := mglobalsDisjointEvaluate s0 [x] xs env1full (.val values) middle
      ⟨argsRun, safe, envSafe, safeParts.2, swappedUnique, fnDisjoint⟩
    have nextStateOracleDisjoint := stateOracleMglobalsDisjointEvaluate xs env1full s0 (.val values) middle
      ⟨argsRun, safe, safeParts.2, envSafe, argsUnique, argsDisjoint, stateOracleDisjoint⟩
    obtain ⟨n, shifted⟩ := evaluateImpShiftSeq xs env1full s0 (.val values) middle argsRun
    have nextCoSyntax : coEveryFnVarsNone middle.compileOracle := by
      rw [shifted]; exact coEveryFnVarsNoneShift s0.compileOracle coSyntax n
    have nextOracleSafe : oracleStateSgcFree middle.compileOracle := by
      rw [shifted]; exact oracleStateSgcFreeShift s0.compileOracle oracleSafe n
    have nextMono := oracleGapproxSubsptEvaluate () xs env1full s0 (.val values) middle ⟨mono, argsRun⟩
    have nextTree := nextGEvaluateSubspt xs env1full s0 (.val values) middle ⟨mono, argsRun⟩
    have nextRel := valueRelListSubspt c (nextG s0) env1 env2 envRel (nextG middle) nextTree
    have optimizerSafe := PreserveSafety.knownPreservesEsgcFree c xs aenv g0 argsEas g1
      ⟨argsKnown, safeParts.2, approxSafe, globalSafe⟩
    have nextOracleApprox := oracleGapproxDisjointLemma xs env1full s0 (.val values) middle
      c aenv g0 argsEas g1 ⟨argsRun, argsKnown, argsUnique, startOracle⟩
    have fnApproxResult := CorrectApprox.Total.knownCorrectApprox c [x] aenv g1 [(fnExp, fnApprox)] g2
      env1 xenv1 middle fnResult next ⟨fnKnown, by simpa [envEq] using fnRun, nextUnique,
        approxRel, argsApprox.1, nextDisjoint, nextOracleApprox, safety.1,
        by simpa [← envEq] using envSafe, fnSafe, approxSafe, optimizerSafe.2.2⟩
    have fnStep := fnIH fnResult next env1 xenv1 env2 xenv2 targetMiddle c g1 g2 aenv [(fnExp, fnApprox)]
      ⟨fnRun, fnKnown, midState, syntaxParts.1, nextCoSyntax, nextDisjoint, midOracle,
        nextStateOracleDisjoint, fnSafe, safety.1, envSafe, approxRel, nextOracleSafe,
        optimizerSafe.2.2, approxSafe, midGlobals, subFn, subsptTrans g2 (nextG s0) (nextG middle) sub1 nextTree,
        nextMono, freeParts.1, nextRel, nextUnique, midStateOracle, envEq, fnNoType⟩
    obtain ⟨targetFnResult, targetNext, targetFnRun, fnRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := fnStep
    have fnTree := nextGEvaluateSubspt [x] env1full middle fnResult next ⟨nextMono, fnRun⟩
    have fnSafety := EvaluateGlobalsPort.Total.evaluateChangedGlobals [x] env1full middle
      fnResult next ⟨fnRun, safety.1, fnSafe, envSafe⟩
    have valuesSafe : ∀ v ∈ values, vsgcFree v := by simpa [rsgcFree] using safety.2.1
    have finalStateOracleDisjoint := stateOracleMglobalsDisjointEvaluate [x] env1full middle
      fnResult next ⟨fnRun, safety.1, fnSafe, envSafe, nextUnique,
        nextDisjoint, nextStateOracleDisjoint⟩
    have finalUnique := uniqueSetGlobalsEvaluate [x] [] env1full middle next fnResult
      ⟨nilUniqueSetGlobals [x] middle.compileOracle nextUnique, fnRun⟩
    obtain ⟨m, fnShifted⟩ := evaluateImpShiftSeq [x] env1full middle fnResult next fnRun
    have finalCoSyntax : coEveryFnVarsNone next.compileOracle := by
      rw [fnShifted]; exact coEveryFnVarsNoneShift middle.compileOracle nextCoSyntax m
    have finalOracleSafe : oracleStateSgcFree next.compileOracle := by
      rw [fnShifted]; exact oracleStateSgcFreeShift middle.compileOracle nextOracleSafe m
    have finalMono := oracleGapproxSubsptEvaluate () [x] env1full middle fnResult next ⟨nextMono, fnRun⟩
    exact ⟨targetValues, targetFnResult, targetMiddle, targetNext, targetArgsRun, by simpa using targetFnRun,
      valueRelListSubspt c (nextG middle) values targetValues argsRel (nextG next) fnTree,
      argsApprox.2 values rfl, fnRel, fnApproxResult.2, fnSafety.1, fnSafety.2.1, valuesSafe, finalOracleSafe, finalCoSyntax,
      finalUnique, finalStateOracleDisjoint, finalMono, finalState, finalGlobals, finalOracle, finalDisjoint⟩

/-- Once both preliminary evaluations succeed, the source application
induction hypothesis applies to either an unchanged call or an annotated call.
This is Flapjack infrastructure for the non-inlining branches. -/
theorem applicationContinuation {C F : Type} (c : Config) (loc targetLoc : Option Nat)
    (fn targetFn : ClosSem.Value) (values targetValues : List ClosSem.Value)
    (next : State (Spt ValApprox × C) F) (targetNext : State C F)
    (approx : ValApprox) (arity : Nat)
    (ih : KnownAppSimulationAt loc fn values next)
    (h : List.Forall₂ (ValueRel c (nextG next)) values targetValues ∧
      ValueRel c (nextG next) fn targetFn ∧ ValApproxVal approx fn ∧
      ssgcFree next ∧ vsgcFree fn ∧ (∀ v ∈ values, vsgcFree v) ∧
      oracleStateSgcFree next.compileOracle ∧ coEveryFnVarsNone next.compileOracle ∧
      uniqueSetGlobals [] next.compileOracle ∧ stateOracleMglobalsDisjoint next ∧
      oracleGapproxSubspt next.compileOracle ∧
      StateRel c (nextG next) next targetNext ∧ stateGlobalsApprox next (nextG next) ∧
      isStateOracle (compileInc c) next.compileOracle ∧
      oracleGapproxDisjoint (nextG next) next.compileOracle)
    (arityEq : arity = values.length)
    (choice : targetLoc = loc ∨ ∃ address, targetLoc = some address ∧
      decideInlineHOL c approx loc arity = .annotate address)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (final : State (Spt ValApprox × C) F)
    (run : evaluateApp loc fn values next = (result, final))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ targetResult targetFinal,
      evaluateApp targetLoc targetFn targetValues targetNext = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG final))) (ValueRel c (nextG final)) result targetResult ∧
      StateRel c (nextG final) final targetFinal ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧
      oracleGapproxDisjoint (nextG final) final.compileOracle := by
  obtain ⟨argsRel, fnRel, sound, safe, fnSafe, argsSafe, oracleSafe, coSyntax,
    unique, disjoint, mono, state, globals, stateOracle, oracle⟩ := h
  have locRel : loptRel targetFn values.length loc targetLoc := by
    rcases choice with equal | ⟨address, rfl, decision⟩
    · exact Or.inl equal
    · simpa [arityEq] using ApplyPartial.annotatedApplicationLocation c (nextG next)
        approx fn targetFn loc arity address decision sound fnRel
  apply ih result final targetLoc targetFn targetValues targetNext c none
  exact ⟨run, by simpa [valueRelAppNone] using fnRel, oracle, disjoint, safe,
    fnSafe, argsSafe, oracleSafe, coSyntax, unique, stateOracle, argsRel, state,
    globals, mono, locRel, by simp, noType⟩

end Flapjack.Compiler.Backend.ClosKnown.Simulation.AppPrefix
