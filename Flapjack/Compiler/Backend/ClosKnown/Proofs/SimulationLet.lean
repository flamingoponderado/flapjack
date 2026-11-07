import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationCons

/-! Let-binding case of the known-function semantic simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Let
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

/-- Let-binding case of the original optimizer simulation, with the source
binding and successful-binding body induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0Let {C F : Type} (trace : BackendCommon.Tra) (xs : List ClosLang.Exp)
    (body : ClosLang.Exp) (env1full : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F)
    (bodyIH : ∀ (bindResult : Result (List ClosSem.Value) ClosSem.Value)
      (middle : State (Spt ValApprox × C) F) (values : List ClosSem.Value),
      evaluate xs env1full s0 = (bindResult, middle) ∧ bindResult = .val values →
      KnownSimulationAt [body] (values ++ env1full) middle)
    (bindIH : KnownSimulationAt xs env1full s0) :
    KnownSimulationAt [.let trace xs body] env1full s0 := by
  intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
  obtain ⟨run, known, state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
    exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
    sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
  have uniqueBoth : uniqueSetGlobals (xs ++ [body]) s0.compileOracle := by
    intro n i
    have bound := unique n i
    simp only [elistGlobals_append, elistGlobals, setGlobals,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag] at bound ⊢
    omega
  have ⟨bindUnique, bodyUnique, swappedUnique⟩ := CorrectApprox.Cons.uniqueParts xs [body] s0.compileOracle uniqueBoth
  have ⟨bindDisjoint, bodyDisjoint⟩ :=
    (mglobalsDisjointRw s0.globals body body body body body xs trace .install [] none none [] 0 0).2.1.mp disjoint
  have syntaxParts : everyFnVarsNone xs ∧ everyFnVarsNone [body] := by
    simpa [everyFnVarsNone, fnVarsNoneExp, and_comm] using inputSyntax
  have safeParts := exprSafe (.let trace xs body) (by simp)
  simp only [esgcFree, esgcFreeList_iff] at safeParts
  have bodySafe : ∀ e ∈ [body], esgcFree e := by simpa using safeParts.2
  have ⟨bindFree, bodyFree⟩ := (fvMaxLet env1.length trace xs body).1 free
  have bagDisjoint : ∀ i, elistGlobals xs i = 0 ∨ elistGlobals [body] i = 0 := by
    intro i
    have bound := uniqueBoth 0 i
    simp only [elistGlobals_append] at bound
    omega
  cases hk : knownListTotal c xs aenv g0 with
  | mk bindEas g1 =>
    cases hb : knownListTotal c [body] (bindEas.map Prod.snd ++ aenv) g1 with
    | mk bodyEas g2 =>
      obtain ⟨be, ba, eq⟩ := knownListTotal_single_result c body (bindEas.map Prod.snd ++ aenv) g1 g2 bodyEas hb
      subst bodyEas
      rw [knownListTotal_let, hk] at known
      dsimp only at known
      rw [hb] at known
      simp [knownSourceHead] at known
      rcases known with ⟨rfl, rfl⟩
      have ⟨subBind, subBody⟩ := subsptKnownElistGlobals c xs aenv g0 bindEas g1
        [body] (bindEas.map Prod.snd ++ aenv) [(be, ba)] g2 ⟨hk, hb, sub0, bagDisjoint⟩
      have subBindNext : sptSubspt g1 (nextG s0) := subsptTrans _ _ _ subBody sub1
      have startSub : sptSubspt g0 (nextG s0) := subsptTrans _ _ _ sub0 sub1
      have startApprox := stateGlobalsApproxSubspt g0 (nextG s0) s0 ⟨startSub, globals⟩
      have startOracle := oracleGapproxDisjointSubspt g0 (nextG s0) s0.compileOracle ⟨startSub, oracle⟩
      cases hr : evaluate xs env1full s0 with
      | mk bindResult middle =>
        rw [evaluate, fixClock_evaluate, hr] at run
        have bindNoType : bindResult ≠ .err (.abort .typeError) := by
          intro eq
          subst bindResult
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact noType rfl
        have bindApprox := CorrectApprox.Total.knownCorrectApprox c xs aenv g0 bindEas g1 env1 xenv1 s0
          bindResult middle ⟨hk, by simpa [envEq] using hr, bindUnique, approxRel, startApprox,
            bindDisjoint, startOracle, safe, by simpa [← envEq] using envSafe, safeParts.1,
            approxSafe, globalSafe⟩
        have bindStep := bindIH bindResult middle env1 xenv1 env2 xenv2 t0 c g0 g1 aenv bindEas
          ⟨hr, hk, state, syntaxParts.1, coSyntax, bindDisjoint, oracle, stateOracleDisjoint,
            safeParts.1, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
            subBind, subBindNext, mono, bindFree, envRel, bindUnique, stateOracle, envEq, bindNoType⟩
        obtain ⟨targetBindResult, targetMiddle, targetBindRun, bindRel, midState, midGlobals, midStateOracle, midOracle⟩ := bindStep
        cases bindResult with
        | err error =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          cases targetBindResult with
          | val values => simp [resultRel] at bindRel
          | err error2 =>
            refine ⟨.err error2, targetMiddle, ?_, bindRel, midState, midGlobals, midStateOracle, midOracle⟩
            simp only [List.map_cons, List.map_nil]
            rw [evaluate, fixClock_evaluate, targetBindRun]
        | val values =>
          cases targetBindResult with
          | err error => simp [resultRel] at bindRel
          | val targetValues =>
            have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals xs env1full s0 (.val values) middle
              ⟨hr, safe, safeParts.1, envSafe⟩
            have valuesSafe : ∀ v ∈ values, vsgcFree v := by simpa [rsgcFree] using safety.2.1
            have nextUnique := uniqueSetGlobalsEvaluate xs [body] env1full s0 middle (.val values) ⟨bodyUnique, hr⟩
            have nextDisjoint := mglobalsDisjointEvaluate s0 [body] xs env1full (.val values) middle
              ⟨hr, safe, envSafe, safeParts.1, swappedUnique, bodyDisjoint⟩
            have nextStateOracleDisjoint := stateOracleMglobalsDisjointEvaluate xs env1full s0 (.val values) middle
              ⟨hr, safe, safeParts.1, envSafe, bindUnique, bindDisjoint, stateOracleDisjoint⟩
            obtain ⟨n, shifted⟩ := evaluateImpShiftSeq xs env1full s0 (.val values) middle hr
            have nextCoSyntax : coEveryFnVarsNone middle.compileOracle := by
              rw [shifted]
              exact coEveryFnVarsNoneShift s0.compileOracle coSyntax n
            have nextOracleSafe : oracleStateSgcFree middle.compileOracle := by
              rw [shifted]
              exact oracleStateSgcFreeShift s0.compileOracle oracleSafe n
            have nextMono : oracleGapproxSubspt middle.compileOracle :=
              oracleGapproxSubsptEvaluate () xs env1full s0 (.val values) middle ⟨mono, hr⟩
            have nextTree := nextGEvaluateSubspt xs env1full s0 (.val values) middle ⟨mono, hr⟩
            have nextRel := valueRelListSubspt c (nextG s0) env1 env2 envRel (nextG middle) nextTree
            have optimizerSafe := PreserveSafety.knownPreservesEsgcFree c xs aenv g0 bindEas g1
              ⟨hk, safeParts.1, approxSafe, globalSafe⟩
            have extendSafe : ∀ v ∈ values ++ env1full, vsgcFree v := by
              simpa [List.mem_append, or_imp, forall_and] using And.intro valuesSafe envSafe
            have extendApproxSafe : ∀ a ∈ bindEas.map Prod.snd ++ aenv, valApproxSgcFree a := by
              simpa [List.mem_append, or_imp, forall_and] using And.intro optimizerSafe.2.1 approxSafe
            have extendApproxRel : List.Forall₂ ValApproxVal (bindEas.map Prod.snd ++ aenv) (values ++ env1) :=
              List.rel_append (bindApprox.2 values rfl) approxRel
            have extendEnvRel : List.Forall₂ (ValueRel c (nextG middle)) (values ++ env1) (targetValues ++ env2) :=
              List.rel_append bindRel nextRel
            have valueLength := evaluate_length.1 xs env1full s0 middle values hr
            have extendedFree : fvMax (values ++ env1).length [body] := by
              simpa [List.length_append, valueLength, Nat.add_comm] using bodyFree
            cases bodyRun : evaluate [body] (values ++ env1full) middle with
            | mk bodyResult last =>
              have bodyNoType : bodyResult ≠ .err (.abort .typeError) := by
                intro eq
                subst bodyResult
                simp [bodyRun] at run
                rcases run with ⟨rfl, rfl⟩
                exact noType rfl
              have bodyStep := bodyIH (.val values) middle values ⟨hr, rfl⟩ bodyResult last
                (values ++ env1) xenv1 (targetValues ++ env2) xenv2 targetMiddle c g1 g2
                (bindEas.map Prod.snd ++ aenv) [(be, ba)]
                ⟨bodyRun, hb, midState, syntaxParts.2, nextCoSyntax, nextDisjoint, midOracle, nextStateOracleDisjoint,
                  bodySafe, safety.1, extendSafe, extendApproxRel, nextOracleSafe, optimizerSafe.2.2, extendApproxSafe,
                  midGlobals, subBody, subsptTrans _ _ _ sub1 nextTree, nextMono, extendedFree, extendEnvRel,
                  nextUnique, midStateOracle, by simpa [List.append_assoc] using congrArg (values ++ ·) envEq, bodyNoType⟩
              obtain ⟨targetBodyResult, targetLast, targetBodyRun, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := bodyStep
              simp only [bodyRun] at run
              cases bodyResult <;> cases run <;>
                refine ⟨targetBodyResult, targetLast, ?_, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ <;>
                simp only [List.map_cons, List.map_nil] <;>
                rw [evaluate, fixClock_evaluate, targetBindRun] <;>
                simpa [List.append_assoc] using targetBodyRun

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Let
