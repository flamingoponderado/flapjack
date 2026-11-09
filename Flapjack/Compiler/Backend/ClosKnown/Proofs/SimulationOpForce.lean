module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationForceArgs

@[expose] public section


/-! Force-operation dispatch in the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Force
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesProps

/-- Simulate force dispatch after successful related argument evaluations.
This is Flapjack induction infrastructure for the full operation case. -/
theorem forceDispatchAfterArguments {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (xs ys : List ClosLang.Exp) (env targetEnv : List Value)
    (initial middle : State (Spt ValApprox × C) F) (targetInitial target : State C F)
    (args targetArgs : List Value)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (final : State (Spt ValApprox × C) F)
    (runArgs : evaluate xs env initial = (.val args, middle))
    (targetRunArgs : evaluate ys targetEnv targetInitial = (.val targetArgs, target))
    (states : StateRel c (nextG middle) middle target)
    (argsRelated : List.Forall₂ (ValueRel c (nextG middle)) args targetArgs)
    (safe : ssgcFree initial) (envSafe : ∀ v ∈ env, vsgcFree v)
    (exprSafe : ∀ e ∈ xs, esgcFree e)
    (oracleSyntax : coEveryFnVarsNone initial.compileOracle)
    (oracleSafe : oracleStateSgcFree initial.compileOracle)
    (disjoint : stateOracleMglobalsDisjoint initial)
    (argsDisjoint : mglobalsDisjoint initial.globals xs)
    (argsUnique : uniqueSetGlobals xs initial.compileOracle)
    (mono : oracleGapproxSubspt initial.compileOracle)
    (middleOracleDisjoint : oracleGapproxDisjoint (nextG middle) middle.compileOracle)
    (middleGlobals : stateGlobalsApprox middle (nextG middle))
    (middleOracle : isStateOracle (compileInc c) middle.compileOracle)
    (ih : ∀ value, destThunk args middle.refs = .isThunk .notEvaluated value →
      KnownSimulationAt [appUnit (.var .none 0)] [value] middle)
    (run : evaluate [.op trace (.thunkOp .forceThunk) xs] env initial = (result, final))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ result' targetFinal,
      evaluate [.op trace (.thunkOp .forceThunk) ys] targetEnv targetInitial = (result', targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG final))) (ValueRel c (nextG final)) result result' ∧
      StateRel c (nextG final) final targetFinal ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧
      oracleGapproxDisjoint (nextG final) final.compileOracle := by
  rw [evaluate, fixClock_evaluate, runArgs] at run
  dsimp only at run
  have destRel := destThunk_related states argsRelated
  cases sourceDest : destThunk args middle.refs with
  | badRef =>
    simp [sourceDest] at run
    rcases run with ⟨rfl, rfl⟩
    exact (noType rfl).elim
  | notThunk =>
    simp [sourceDest] at run
    rcases run with ⟨rfl, rfl⟩
    exact (noType rfl).elim
  | isThunk mode value =>
    rw [sourceDest] at destRel
    cases targetDest : destThunk targetArgs target.refs with
    | badRef => rw [targetDest] at destRel; cases destRel
    | notThunk => rw [targetDest] at destRel; cases destRel
    | isThunk targetMode other =>
      rw [targetDest] at destRel
      cases destRel with
      | isThunk _ _ _ valueRelated =>
        cases mode with
        | evaluated =>
          simp [sourceDest] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨.val [other], target, ?_, ?_, states, middleGlobals, middleOracle, middleOracleDisjoint⟩
          · rw [evaluate, fixClock_evaluate, targetRunArgs]
            simp [targetDest]
          · exact .cons valueRelated .nil
        | notEvaluated =>
          simp only [sourceDest] at run
          cases bodyRun : evaluate [appUnit (.var .none 0)] [value] middle with
          | mk bodyResult last =>
            rw [bodyRun] at run
            cases bodyResult with
            | err error =>
              simp at run
              rcases run with ⟨rfl, rfl⟩
              have step := forceBodyAfterArguments c xs env initial middle target args targetArgs value
                (.err error) last runArgs states argsRelated sourceDest safe envSafe exprSafe oracleSyntax
                oracleSafe disjoint argsDisjoint argsUnique mono middleOracleDisjoint middleGlobals
                middleOracle (ih value sourceDest) bodyRun noType
              obtain ⟨other', targetResult, targetLast, targetFound, targetBody, resultRel,
                finalState, finalGlobals, finalOracle, finalDisjoint⟩ := step
              rw [targetDest] at targetFound
              cases targetFound
              cases targetResult with
              | val vals => simp [Flapjack.SemanticPrimitivesProps.resultRel] at resultRel
              | err error' =>
                refine ⟨.err error', targetLast, ?_, resultRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩
                rw [evaluate, fixClock_evaluate, targetRunArgs]
                simp [targetDest, targetBody]
            | val forced =>
              dsimp only at run
              cases update : updateThunk args last.refs forced with
              | none =>
                simp [update] at run
                rcases run with ⟨rfl, rfl⟩
                exact (noType rfl).elim
              | some refs =>
                simp [update] at run
                rcases run with ⟨rfl, rfl⟩
                obtain ⟨other', forced', targetLast, targetRefs, targetFound, targetBody, targetUpdate,
                  values, finalState, finalGlobals, finalOracle, finalDisjoint⟩ :=
                  forceUpdateAfterArguments c xs env initial middle target args targetArgs value forced last refs
                    runArgs states argsRelated sourceDest safe envSafe exprSafe oracleSyntax oracleSafe
                    disjoint argsDisjoint argsUnique mono middleOracleDisjoint middleGlobals middleOracle
                    (ih value sourceDest) bodyRun update
                rw [targetDest] at targetFound
                cases targetFound
                refine ⟨.val forced', { targetLast with refs := targetRefs }, ?_, values,
                  finalState, finalGlobals, finalOracle, finalDisjoint⟩
                rw [evaluate, fixClock_evaluate, targetRunArgs]
                simp [targetDest, targetBody, targetUpdate]

/-- Simulate the complete force dispatch after related argument evaluations,
including argument errors and the optimizer's smart-operation output. This
is Flapjack induction infrastructure for the force-operation case. -/
theorem forceSmartOpAfterArguments {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (xs ys : List ClosLang.Exp) (env targetEnv : List Value)
    (initial middle : State (Spt ValApprox × C) F) (targetInitial target : State C F)
    (argResult targetArgResult result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (final : State (Spt ValApprox × C) F)
    (runArgs : evaluate xs env initial = (argResult, middle))
    (targetRunArgs : evaluate ys targetEnv targetInitial = (targetArgResult, target))
    (states : StateRel c (nextG middle) middle target)
    (argsRelated : resultRel (List.Forall₂ (ValueRel c (nextG middle)))
      (ValueRel c (nextG middle)) argResult targetArgResult)
    (safe : ssgcFree initial) (envSafe : ∀ v ∈ env, vsgcFree v)
    (exprSafe : ∀ e ∈ xs, esgcFree e)
    (oracleSyntax : coEveryFnVarsNone initial.compileOracle)
    (oracleSafe : oracleStateSgcFree initial.compileOracle)
    (disjoint : stateOracleMglobalsDisjoint initial)
    (argsDisjoint : mglobalsDisjoint initial.globals xs)
    (argsUnique : uniqueSetGlobals xs initial.compileOracle)
    (mono : oracleGapproxSubspt initial.compileOracle)
    (middleOracleDisjoint : oracleGapproxDisjoint (nextG middle) middle.compileOracle)
    (middleGlobals : stateGlobalsApprox middle (nextG middle))
    (middleOracle : isStateOracle (compileInc c) middle.compileOracle)
    (ih : ∀ args value, argResult = .val args →
      destThunk args middle.refs = .isThunk .notEvaluated value →
      KnownSimulationAt [appUnit (.var .none 0)] [value] middle)
    (run : evaluate [.op trace (.thunkOp .forceThunk) xs] env initial = (result, final))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ result' targetFinal,
      evaluate [ClosOp.smartOp trace (.thunkOp .forceThunk) ys] targetEnv targetInitial = (result', targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG final))) (ValueRel c (nextG final)) result result' ∧
      StateRel c (nextG final) final targetFinal ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧
      oracleGapproxDisjoint (nextG final) final.compileOracle := by
  have raw : ∃ result' targetFinal,
      evaluate [.op trace (.thunkOp .forceThunk) ys] targetEnv targetInitial = (result', targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG final))) (ValueRel c (nextG final)) result result' ∧
      StateRel c (nextG final) final targetFinal ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧
      oracleGapproxDisjoint (nextG final) final.compileOracle := by
    cases argResult with
    | err error =>
      cases targetArgResult with
      | val targetArgs => simp [resultRel] at argsRelated
      | err targetError =>
        rw [evaluate, fixClock_evaluate, runArgs] at run
        simp at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨.err targetError, target, ?_, argsRelated, states, middleGlobals, middleOracle, middleOracleDisjoint⟩
        rw [evaluate, fixClock_evaluate, targetRunArgs]
    | val args =>
      cases targetArgResult with
      | err error => simp [resultRel] at argsRelated
      | val targetArgs =>
        exact forceDispatchAfterArguments c trace xs ys env targetEnv initial middle targetInitial target
          args targetArgs result final runArgs targetRunArgs states argsRelated safe envSafe exprSafe
          oracleSyntax oracleSafe disjoint argsDisjoint argsUnique mono middleOracleDisjoint
          middleGlobals middleOracle (fun value found => ih args value rfl found) run noType
  obtain ⟨result', targetFinal, targetRun, related, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := raw
  have targetNoType : result' ≠ .err (.abort .typeError) := by
    intro eq
    subst result'
    cases result with
    | val values => simp [resultRel] at related
    | err error =>
      cases error with
      | raise value => simp [resultRel, excRel] at related
      | abort abort =>
        simp [resultRel, excRel] at related
        subst abort
        exact noType rfl
  exact ⟨result', targetFinal, ClosOp.smartOpThm trace (.thunkOp .forceThunk) ys targetEnv
    targetInitial targetFinal result' ⟨targetRun, targetNoType⟩, related, finalState,
    finalGlobals, finalOracle, finalDisjoint⟩

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Force-operation case of the optimizer simulation, assuming exactly the
argument and forced-body induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0OpForce {C F : Type} (trace : BackendCommon.Tra)
    (xs : List ClosLang.Exp) (env1full : List Value)
    (s0 : ClosSem.State (Spt ValApprox × C) F)
    (forceIH : ∀ (args : List Value) (middle : ClosSem.State (Spt ValApprox × C) F) value,
      evaluate xs env1full s0 = (.val args, middle) →
      destThunk args middle.refs = .isThunk .notEvaluated value →
      KnownSimulationAt [appUnit (.var .none 0)] [value] middle)
    (argsIH : KnownSimulationAt xs env1full s0) :
    KnownSimulationAt [.op trace (.thunkOp .forceThunk) xs] env1full s0 := by
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
    have safeOp := exprSafe (.op trace (.thunkOp .forceThunk) xs) (by simp)
    simpa [esgcFree, esgcFreeList_iff] using safeOp
  have argsSyntax : everyFnVarsNone xs := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
  have argsFree : fvMax env1.length xs := by
    simpa [fvMax, freeVars, freeVarExp] using free
  cases hk : knownListTotal c xs aenv g0 with
  | mk argEas g1 =>
    rw [knownListTotal_op, hk] at known
    simp [knownOpHOL] at known
    rcases known with ⟨rfl, rfl⟩
    cases hr : evaluate xs env1full s0 with
    | mk argResult middle =>
      have argsNoType : argResult ≠ .err (.abort .typeError) := by
        intro eq
        subst argResult
        rw [evaluate, fixClock_evaluate, hr] at run
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact noType rfl
      obtain ⟨targetArgResult, targetMiddle, targetArgs, argsRelated, midState, midGlobals,
          midOracleState, midOracle⟩ := argsIH argResult middle env1 xenv1 env2 xenv2 t0 c g0 g1
        aenv argEas ⟨hr, hk, state, argsSyntax, coSyntax, argsDisjoint, oracle, stateOracleDisjoint,
          argsSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
          sub0, sub1, mono, argsFree, envRel, argsUnique, stateOracle, envEq, argsNoType⟩
      have step := forceSmartOpAfterArguments c trace xs (argEas.map Prod.fst) env1full (env2 ++ xenv2)
        s0 middle t0 targetMiddle argResult targetArgResult res1 s hr targetArgs midState argsRelated
        safe envSafe argsSafe coSyntax oracleSafe stateOracleDisjoint argsDisjoint argsUnique mono
        midOracle midGlobals midOracleState (fun args value eq found => by
          subst argResult
          exact forceIH args middle value hr found) run noType
      simpa using step

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Force
