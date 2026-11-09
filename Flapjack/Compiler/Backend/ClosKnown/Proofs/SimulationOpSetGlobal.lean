module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationOpOrdinary

@[expose] public section


/-! Global-write case of known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.SetGlobal
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint SubsptComposition
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesProps

/-- A successful global write preserves agreement with a larger approximation
tree containing the optimizer's result. This is Flapjack induction
infrastructure for the global-write case. -/
theorem setGlobalApproxAfter {C F : Type} (index : Nat)
    (approxs : List ValApprox) (g0 g : Spt ValApprox) (a : ValApprox)
    (values : List Value) (middle next : State C F) (v : Value) (tree : Spt ValApprox)
    (known : knownOpHOL (.globOp (.setGlobal index)) approxs g0 = (a, g))
    (run : doApp (.globOp (.setGlobal index)) values middle = .val (v, next))
    (rel : List.Forall₂ ValApproxVal approxs values)
    (globals : stateGlobalsApprox middle tree) (g0sub : sptSubspt g0 g) (sub : sptSubspt g tree) :
    stateGlobalsApprox next tree := by
  have smaller : stateGlobalsApprox middle g0 := by
    have composed : sptSubspt g0 tree := by
      intro k member
      obtain ⟨mid, eq1⟩ := g0sub k member
      obtain ⟨last, eq2⟩ := sub k mid
      exact ⟨last, eq2.trans eq1⟩
    exact stateGlobalsApproxSubspt g0 tree middle ⟨composed, globals⟩
  have writtenApprox := (KnownOpCorrect.knownOpCorrectApproxSetGlobal index approxs g0 a g
    values middle v next known run rel smaller).1
  have indexMem : sptMem index g := by
    cases approxs with
    | nil =>
      cases rel
      simp [doApp, applyGlobal] at run
    | cons first rest =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      obtain ⟨_, rfl⟩ := known
      simp [sptMem_sptInsert]
  have eqLookup := (sub index indexMem).2
  have frame := doAppMglobals (.globOp (.setGlobal index)) values middle next v run
  intro k value approx ⟨found, lookup⟩
  by_cases same : k = index
  · subst k
    apply writtenApprox index value approx
    exact ⟨found, eqLookup.symm.trans lookup⟩
  · apply globals k value approx
    exact ⟨frame.2 k value ⟨found, by simp [opGlobalBag, same]⟩, lookup⟩

/-- Evaluating a global-write operation preserves the final-state simulation
invariants, using the optimizer's argument approximations. This is Flapjack
induction infrastructure. -/
theorem setGlobalStateInvariants {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (xs : List ClosLang.Exp) (env : List Value) (s0 middle final : State (Spt ValApprox × C) F)
    (argResult result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (argEas : List (ClosLang.Exp × ValApprox)) (g1 g2 : Spt ValApprox) (a : ValApprox)
    (known : knownOpHOL (.globOp (.setGlobal index)) (argEas.map Prod.snd).reverse g1 = (a, g2))
    (subOp : sptSubspt g1 g2) (subNext : sptSubspt g2 (nextG middle))
    (argsRun : evaluate xs env s0 = (argResult, middle))
    (argsApprox : ∀ values, argResult = .val values →
      List.Forall₂ ValApproxVal (argEas.map Prod.snd) values)
    (run : evaluate [.op trace (.globOp (.setGlobal index)) xs] env s0 = (result, final))
    (globals : stateGlobalsApprox middle (nextG middle))
    (oracle : isStateOracle (compileInc c) middle.compileOracle)
    (oracleDisjoint : oracleGapproxDisjoint (nextG middle) middle.compileOracle) :
    nextG final = nextG middle ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧
      oracleGapproxDisjoint (nextG final) final.compileOracle := by
  rw [evaluate_ordinaryOp_eq trace (.globOp (.setGlobal index)) xs env s0 (by simp) (by simp), argsRun] at run
  cases argResult with
  | err error =>
    simp at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨rfl, globals, oracle, oracleDisjoint⟩
  | val values =>
    cases app : doApp (.globOp (.setGlobal index)) values.reverse middle with
    | err error =>
      simp [app] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨rfl, globals, oracle, oracleDisjoint⟩
    | val pair =>
      rcases pair with ⟨value, next⟩
      simp [app] at run
      rcases run with ⟨rfl, rfl⟩
      have oracleEq := (doApp_codeOracle _ _ _ _ _ app).2
      have valueRel := List.rel_reverse (argsApprox values rfl)
      have globalNext := setGlobalApproxAfter index (argEas.map Prod.snd).reverse g1 g2 a
        values.reverse middle next value (nextG middle) known app valueRel globals subOp subNext
      have nextEq : nextG next = nextG middle := by simp [nextG, oracleEq]
      exact ⟨nextEq, by simpa [nextEq] using globalNext, by simpa [oracleEq] using oracle,
        by simpa [nextEq, oracleEq] using oracleDisjoint⟩

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Global-write case of the optimizer simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0OpSetGlobal {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (xs : List ClosLang.Exp) (env1full : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (argsIH : KnownSimulationAt xs env1full s0) : KnownSimulationAt [.op trace (.globOp (.setGlobal index)) xs] env1full s0 := by
  intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
  obtain ⟨run, known, state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
    exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
    sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
  have argsUnique : uniqueSetGlobals xs s0.compileOracle := by
    intro n k
    have bound := unique n k
    simp only [elistGlobals_append, elistGlobals, setGlobals,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag] at bound ⊢
    omega
  have argsDisjoint : mglobalsDisjoint s0.globals xs := by
    have parts := (mglobalsDisjointRw s0.globals (.var .none 0) (.var .none 0)
      (.var .none 0) (.var .none 0) (.var .none 0) xs trace (.globOp (.setGlobal index))
      [] none none [] 0 0).2.2.2.2.2.2.2.1
    exact (parts.mp disjoint).1
  have argsSafe : ∀ e ∈ xs, esgcFree e := by
    have safeOp := exprSafe (.op trace (.globOp (.setGlobal index)) xs) (by simp)
    simpa [esgcFree, esgcFreeList_iff] using safeOp
  have argsSyntax : everyFnVarsNone xs := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
  have argsFree : fvMax env1.length xs := by
    simpa [fvMax, freeVars, freeVarExp] using free
  cases hk : knownListTotal c xs aenv g0 with
  | mk argEas g1 =>
    cases ho : knownOpHOL (.globOp (.setGlobal index)) (argEas.map Prod.snd).reverse g1 with
    | mk a g2 =>
      rw [knownListTotal_op, hk] at known
      dsimp only at known
      rw [ho] at known
      dsimp only at known
      change ([(Ordinary.selectedOutput trace (.globOp (.setGlobal index)) a (argEas.map Prod.fst), a)], g2) = (eas, g) at known
      change ([(ClosOp.smartOp trace (.globOp (.setGlobal index)) (argEas.map Prod.fst), a)], g2) = (eas, g) at known
      simp only [Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      have ⟨subArgs, subOp⟩ := subsptKnownOpElistGlobals c xs aenv g0 argEas g1
        (.globOp (.setGlobal index)) (argEas.map Prod.snd).reverse g2 a ⟨hk, ho, sub0, by
          intro k
          have bound := unique 0 k
          simp only [elistGlobals_append, elistGlobals, setGlobals,
            FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, firstNExps, Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag] at bound
          omega⟩
      have subArgsNext : sptSubspt g1 (nextG s0) := by
        intro key member
        obtain ⟨mid, eq1⟩ := subOp key member
        obtain ⟨last, eq2⟩ := sub1 key mid
        exact ⟨last, eq2.trans eq1⟩
      cases hr : evaluate xs env1full s0 with
      | mk argResult middle =>
        have argsNoType : argResult ≠ .err (.abort .typeError) := by
          intro eq
          subst argResult
          rw [evaluate_ordinaryOp_eq trace (.globOp (.setGlobal index)) xs env1full s0 (by simp) (by simp), hr] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact noType rfl
        obtain ⟨targetArgResult, targetMiddle, targetArgs, argsRelated, midState, midGlobals,
            midOracleState, midOracle⟩ := argsIH argResult middle env1 xenv1 env2 xenv2 t0 c g0 g1
          aenv argEas ⟨hr, hk, state, argsSyntax, coSyntax, argsDisjoint, oracle, stateOracleDisjoint,
            argsSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
            subArgs, subArgsNext, mono, argsFree, envRel, argsUnique, stateOracle, envEq, argsNoType⟩
        obtain ⟨targetResult, targetFinal, targetRun, resultRelated, finalState⟩ :=
          Relations.StateRelation.ordinarySmartOpSimulation c (nextG middle) trace (.globOp (.setGlobal index)) xs
            (argEas.map Prod.fst) env1full (env2 ++ xenv2) s0 middle t0 targetMiddle
            argResult targetArgResult (by simp) (by simp) hr targetArgs argsRelated midState res1 s run noType
        have startSub : sptSubspt g0 (nextG s0) := by
          intro key member
          obtain ⟨mid, eq1⟩ := sub0 key member
          obtain ⟨last, eq2⟩ := sub1 key mid
          exact ⟨last, eq2.trans eq1⟩
        have startGlobals := stateGlobalsApproxSubspt g0 (nextG s0) s0 ⟨startSub, globals⟩
        have startOracle := oracleGapproxDisjointSubspt g0 (nextG s0) s0.compileOracle ⟨startSub, oracle⟩
        have argApprox := CorrectApprox.Total.knownCorrectApprox c xs aenv g0 argEas g1 env1 xenv1 s0
          argResult middle ⟨hk, by simpa [envEq] using hr, argsUnique, approxRel, startGlobals,
            argsDisjoint, startOracle, safe, by simpa [← envEq] using envSafe, argsSafe, approxSafe, globalSafe⟩
        have nextTree := nextGEvaluateSubspt xs env1full s0 argResult middle ⟨mono, hr⟩
        have subNext : sptSubspt g2 (nextG middle) := by
          intro key member
          obtain ⟨mid, eq1⟩ := sub1 key member
          obtain ⟨last, eq2⟩ := nextTree key mid
          exact ⟨last, eq2.trans eq1⟩
        have ⟨nextEq, finalGlobals, finalOracle, finalDisjoint⟩ :=
          setGlobalStateInvariants trace index xs env1full s0 middle s argResult res1 argEas g1 g2 a
            ho subOp subNext hr argApprox.2 run midGlobals midOracleState midOracle
        exact ⟨targetResult, targetFinal, by simpa using targetRun,
          by simpa [nextEq] using resultRelated, by simpa [nextEq] using finalState,
          finalGlobals, finalOracle, finalDisjoint⟩


end Flapjack.Compiler.Backend.ClosKnown.Simulation.SetGlobal
