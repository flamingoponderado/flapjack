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


end Flapjack.Compiler.Backend.ClosKnown.Simulation.Force
