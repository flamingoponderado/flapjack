module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationOpSetGlobal

@[expose] public section


/-! Global-read replacement in known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Global
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint SubsptComposition
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesProps

/-- A global read can fail only with a type error. This is Flapjack proof
infrastructure for the optimizer's constant-replacement cases. -/
theorem globalReadError {C F : Type} (index : Nat) (values : List Value)
    (s : State C F) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult Value)
    (run : doApp (.globOp (.global index)) values s = .err error) :
    error = .abort .typeError := by
  cases found : applyGlobal (.global index) values s with
  | none => simpa [doApp, found] using run.symm
  | some pair => simp [doApp, found] at run

/-- Simulate replacing a global read with an ordinary operation, given the
primitive-level replacement property. This is Flapjack induction infrastructure. -/
theorem globalReplacementSimulation {C F : Type} (c : Config) (tree : Spt ValApprox)
    (trace : BackendCommon.Tra) (index : Nat) (replacement : ClosLang.Op)
    (xs ys : List ClosLang.Exp) (env targetEnv : List Value)
    (s0 middle : State (Spt ValApprox × C) F) (t0 target : State C F)
    (argResult targetArgResult result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (final : State (Spt ValApprox × C) F)
    (notInstall : replacement ≠ .install) (notForce : replacement ≠ .thunkOp .forceThunk)
    (argsRun : evaluate xs env s0 = (argResult, middle))
    (targetArgsRun : evaluate ys targetEnv t0 = (targetArgResult, target))
    (states : StateRel c tree middle target)
    (argsRelated : resultRel (List.Forall₂ (ValueRel c tree)) (ValueRel c tree) argResult targetArgResult)
    (replace : ∀ vs ws next value, argResult = .val vs → List.Forall₂ (ValueRel c tree) vs.reverse ws →
      doApp (.globOp (.global index)) vs.reverse middle = .val (value, next) →
      next = middle ∧ doApp replacement ws target = .val (value, target) ∧ ValueRel c tree value value)
    (run : evaluate [.op trace (.globOp (.global index)) xs] env s0 = (result, final))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ result' targetFinal,
      evaluate [.op trace replacement ys] targetEnv t0 = (result', targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c tree)) (ValueRel c tree) result result' ∧
      StateRel c tree final targetFinal := by
  rw [evaluate_ordinaryOp_eq trace (.globOp (.global index)) xs env s0 (by simp) (by simp), argsRun] at run
  rw [evaluate_ordinaryOp_eq trace replacement ys targetEnv t0 notInstall notForce, targetArgsRun]
  cases argResult with
  | err error =>
    cases targetArgResult with
    | val values => simp [resultRel] at argsRelated
    | err other =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨.err other, target, rfl, argsRelated, states⟩
  | val values =>
    cases targetArgResult with
    | err error => simp [resultRel] at argsRelated
    | val targetValues =>
      cases app : doApp (.globOp (.global index)) values.reverse middle with
      | err error =>
        simp [app] at run
        rcases run with ⟨rfl, rfl⟩
        have eq := globalReadError index values.reverse middle error app
        subst error
        exact (noType rfl).elim
      | val pair =>
        rcases pair with ⟨value, next⟩
        simp [app] at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨rfl, targetApp, related⟩ := replace values targetValues.reverse next value rfl
          (List.rel_reverse argsRelated) app
        dsimp only
        rw [targetApp]
        exact ⟨.val [value], target, rfl, .cons related .nil, states⟩

/-- Simulate the actual optimizer output for a global read, including
integer and empty-constructor replacement. This is Flapjack infrastructure. -/
theorem globalSelectedSimulation {C F : Type} (c : Config) (tree : Spt ValApprox)
    (trace : BackendCommon.Tra) (index : Nat) (a : ValApprox) (g0 g : Spt ValApprox)
    (argEas : List (ClosLang.Exp × ValApprox)) (xs : List ClosLang.Exp) (env targetEnv : List Value)
    (s0 middle : State (Spt ValApprox × C) F) (t0 target : State C F)
    (argResult targetArgResult result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (final : State (Spt ValApprox × C) F)
    (known : knownOpHOL (.globOp (.global index)) (argEas.map Prod.snd).reverse g0 = (a, g))
    (argsRun : evaluate xs env s0 = (argResult, middle))
    (targetArgsRun : evaluate (argEas.map Prod.fst) targetEnv t0 = (targetArgResult, target))
    (states : StateRel c tree middle target)
    (argsRelated : resultRel (List.Forall₂ (ValueRel c tree)) (ValueRel c tree) argResult targetArgResult)
    (argsApprox : ∀ values, argResult = .val values → List.Forall₂ ValApproxVal (argEas.map Prod.snd) values)
    (globals : stateGlobalsApprox middle g0)
    (run : evaluate [.op trace (.globOp (.global index)) xs] env s0 = (result, final))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ result' targetFinal,
      evaluate [Ordinary.selectedOutput trace (.globOp (.global index)) a (argEas.map Prod.fst)]
        targetEnv t0 = (result', targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c tree)) (ValueRel c tree) result result' ∧
      StateRel c tree final targetFinal := by
  have fallback := Relations.StateRelation.ordinarySmartOpSimulation c tree trace (.globOp (.global index))
    xs (argEas.map Prod.fst) env targetEnv s0 middle t0 target argResult targetArgResult
    (by simp) (by simp) argsRun targetArgsRun argsRelated states result final run noType
  cases a with
  | int i =>
    apply globalReplacementSimulation c tree trace index (.intOp (.const i)) xs (argEas.map Prod.fst)
      env targetEnv s0 middle t0 target argResult targetArgResult result final (by simp) (by simp)
      argsRun targetArgsRun states argsRelated ?_ run noType
    intro vs ws next value eq rel app
    have approx := List.rel_reverse (argsApprox vs eq)
    obtain ⟨_, _, _, stateEq, valueEq⟩ := knownGlobalIntShape index (argEas.map Prod.snd).reverse
      g0 g i vs.reverse middle next value known approx globals app
    have targetApp := (knownGlobalIntReplacement c tree index (argEas.map Prod.snd).reverse
      g0 g i vs.reverse ws middle next target value known approx rel globals app).2.2
    subst value
    exact ⟨stateEq, targetApp, .number i⟩
  | tuple tag elements =>
    cases elements with
    | nil =>
      apply globalReplacementSimulation c tree trace index (.blockOp (.cons tag)) xs (argEas.map Prod.fst)
        env targetEnv s0 middle t0 target argResult targetArgResult result final (by simp) (by simp)
        argsRun targetArgsRun states argsRelated ?_ run noType
      intro vs ws next value eq rel app
      have approx := List.rel_reverse (argsApprox vs eq)
      obtain ⟨_, _, _, stateEq, valueEq⟩ := knownGlobalEmptyTupleShape index (argEas.map Prod.snd).reverse
        g0 g tag vs.reverse middle next value known approx globals app
      have targetApp := (knownGlobalEmptyTupleReplacement c tree index (argEas.map Prod.snd).reverse
        g0 g tag vs.reverse ws middle next target value known approx rel globals app).2.2
      subst value
      exact ⟨stateEq, targetApp, .block tag [] [] .nil⟩
    | cons first rest => simpa [Ordinary.selectedOutput] using fallback
  | _ => simpa [Ordinary.selectedOutput] using fallback

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Global-read case of the optimizer simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0OpGlobal {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (xs : List ClosLang.Exp) (env1full : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (argsIH : KnownSimulationAt xs env1full s0) : KnownSimulationAt [.op trace (.globOp (.global index)) xs] env1full s0 := by
  intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
  obtain ⟨run, known, state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
    exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
    sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
  have argsUnique : uniqueSetGlobals xs s0.compileOracle := by
    simpa [uniqueSetGlobals, elistGlobals_append, elistGlobals, setGlobals, opGlobalBag,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using unique
  have argsDisjoint : mglobalsDisjoint s0.globals xs := by
    simpa [mglobalsDisjoint, elistGlobals, setGlobals, opGlobalBag,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using disjoint
  have argsSafe : ∀ e ∈ xs, esgcFree e := by
    have safeOp := exprSafe (.op trace (.globOp (.global index)) xs) (by simp)
    simpa [esgcFree, esgcFreeList_iff] using safeOp
  have argsSyntax : everyFnVarsNone xs := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
  have argsFree : fvMax env1.length xs := by
    simpa [fvMax, freeVars, freeVarExp] using free
  cases hk : knownListTotal c xs aenv g0 with
  | mk argEas g1 =>
    cases ho : knownOpHOL (.globOp (.global index)) (argEas.map Prod.snd).reverse g1 with
    | mk a g2 =>
      rw [knownListTotal_op, hk] at known
      dsimp only at known
      rw [ho] at known
      dsimp only at known
      change ([(Ordinary.selectedOutput trace (.globOp (.global index)) a (argEas.map Prod.fst), a)], g2) = (eas, g) at known
      simp only [Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      have ⟨subArgs, subOp⟩ := subsptKnownOpElistGlobals c xs aenv g0 argEas g1
        (.globOp (.global index)) (argEas.map Prod.snd).reverse g2 a ⟨hk, ho, sub0, by simp [opGlobalBag, FlatProps.emptyGlobalBag, Flapjack.emptyBag]⟩
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
          rw [evaluate_ordinaryOp_eq trace (.globOp (.global index)) xs env1full s0 (by simp) (by simp), hr] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact noType rfl
        obtain ⟨targetArgResult, targetMiddle, targetArgs, argsRelated, midState, midGlobals,
            midOracleState, midOracle⟩ := argsIH argResult middle env1 xenv1 env2 xenv2 t0 c g0 g1
          aenv argEas ⟨hr, hk, state, argsSyntax, coSyntax, argsDisjoint, oracle, stateOracleDisjoint,
            argsSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
            subArgs, subArgsNext, mono, argsFree, envRel, argsUnique, stateOracle, envEq, argsNoType⟩
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
        have subMiddle : sptSubspt g1 (nextG middle) := by
          intro key member
          obtain ⟨mid, eq1⟩ := subArgsNext key member
          obtain ⟨last, eq2⟩ := nextTree key mid
          exact ⟨last, eq2.trans eq1⟩
        have middleApprox := stateGlobalsApproxSubspt g1 (nextG middle) middle ⟨subMiddle, midGlobals⟩
        obtain ⟨targetResult, targetFinal, targetRun, resultRelated, finalState⟩ :=
          globalSelectedSimulation c (nextG middle) trace index a g1 g2 argEas xs env1full (env2 ++ xenv2)
            s0 middle t0 targetMiddle argResult targetArgResult res1 s ho hr targetArgs midState
            argsRelated argApprox.2 middleApprox run noType
        have ⟨nextEq, finalGlobals, finalOracle, finalDisjoint⟩ :=
          Ordinary.ordinaryOpStateInvariants trace (.globOp (.global index)) xs env1full s0 middle s
            argResult res1 (by simp) (by simp) (by simp [opGlobalBag, FlatProps.emptyGlobalBag, Flapjack.emptyBag])
            hr run midGlobals midOracleState midOracle
        exact ⟨targetResult, targetFinal, by simpa using targetRun,
          by simpa [nextEq] using resultRelated, by simpa [nextEq] using finalState,
          finalGlobals, finalOracle, finalDisjoint⟩


end Flapjack.Compiler.Backend.ClosKnown.Simulation.Global
