import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationForceBody
import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationLet

/-! Force-body induction after evaluation of operation arguments. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Force
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesProps

/-- The force payload is safe when it is read from a safe source state.
This is Flapjack proof infrastructure. -/
theorem forcedPayloadSafe {C F : Type} (args : List Value)
    (source : State C F) (mode : AstHOL.ThunkMode) (value : Value)
    (safe : ssgcFree source) (found : destThunk args source.refs = .isThunk mode value) :
    vsgcFree value := by
  unfold ClosSem.destThunk at found
  repeat' split at found
  all_goals simp_all
  exact safe.2.2.1 _ _ _ (by assumption)

/-- After evaluating force arguments, the original body induction hypothesis
can be invoked using only the invariants of the original state and the
intermediate relation furnished by the argument induction hypothesis. This is
Flapjack proof infrastructure for the force operation. -/
theorem forceBodyAfterArguments {C F : Type} (c : Config)
    (xs : List ClosLang.Exp) (env : List Value)
    (initial middle : State (Spt ValApprox × C) F) (target : State C F)
    (args targetArgs : List Value) (value : Value)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (final : State (Spt ValApprox × C) F)
    (runArgs : evaluate xs env initial = (.val args, middle))
    (states : StateRel c (nextG middle) middle target)
    (argsRelated : List.Forall₂ (ValueRel c (nextG middle)) args targetArgs)
    (found : destThunk args middle.refs = .isThunk .notEvaluated value)
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
    (ih : KnownSimulationAt [appUnit (.var .none 0)] [value] middle)
    (run : evaluate [appUnit (.var .none 0)] [value] middle = (result, final))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ other result' targetFinal,
      destThunk targetArgs target.refs = .isThunk .notEvaluated other ∧
      evaluate [appUnit (.var .none 0)] [other] target = (result', targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG final))) (ValueRel c (nextG final)) result result' ∧
      StateRel c (nextG final) final targetFinal ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧
      oracleGapproxDisjoint (nextG final) final.compileOracle := by
  have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals xs env initial (.val args) middle
    ⟨runArgs, safe, exprSafe, envSafe⟩
  have valueSafe := forcedPayloadSafe args middle .notEvaluated value safety.1 found
  have related := destThunk_related states argsRelated
  rw [found] at related
  cases targetFound : destThunk targetArgs target.refs with
  | badRef => rw [targetFound] at related; cases related
  | notThunk => rw [targetFound] at related; cases related
  | isThunk mode other =>
    rw [targetFound] at related
    cases related with
    | isThunk _ _ _ valueRelated =>
      have midDisjoint := stateOracleMglobalsDisjointEvaluate xs env initial (.val args) middle
        ⟨runArgs, safe, exprSafe, envSafe, argsUnique, argsDisjoint, disjoint⟩
      obtain ⟨n, shifted⟩ := evaluateImpShiftSeq xs env initial (.val args) middle runArgs
      have midSyntax : coEveryFnVarsNone middle.compileOracle := by
        rw [shifted]
        exact coEveryFnVarsNoneShift initial.compileOracle oracleSyntax n
      have midSafe : oracleStateSgcFree middle.compileOracle := by
        rw [shifted]
        exact oracleStateSgcFreeShift initial.compileOracle oracleSafe n
      have midMono := oracleGapproxSubsptEvaluate () xs env initial (.val args) middle ⟨mono, runArgs⟩
      have emptyUnique : uniqueSetGlobals [] initial.compileOracle := by
        intro i key
        have bound := argsUnique i key
        change elistGlobals ((firstNExps initial.compileOracle i).flatten) key ≤ 1
        simp only [elistGlobals_append] at bound
        omega
      have midUnique := uniqueSetGlobalsEvaluate xs [] env initial middle (.val args) ⟨emptyUnique, runArgs⟩
      obtain ⟨result', targetFinal, targetRun, resultRelated, finalState, finalGlobals,
        finalOracle, finalDisjoint⟩ := forceBodySimulation c middle target value other result final
          states valueRelated safety.1 valueSafe midSyntax midSafe midDisjoint middleOracleDisjoint
          midMono midUnique middleGlobals middleOracle ih run noType
      exact ⟨other, result', targetFinal, rfl, targetRun, resultRelated,
        finalState, finalGlobals, finalOracle, finalDisjoint⟩

/-- A successful thunk inspection identifies the same pointer in both
related argument lists. This is Flapjack proof infrastructure. -/
theorem relatedThunkPointers {C F : Type} (c : Config) (g : Spt ValApprox)
    (source : State C F) (args targetArgs : List Value)
    (mode : AstHOL.ThunkMode) (value : Value)
    (related : List.Forall₂ (ValueRel c g) args targetArgs)
    (found : destThunk args source.refs = .isThunk mode value) :
    ∃ flag key, args = [.refPtr flag key] ∧ targetArgs = [.refPtr flag key] := by
  cases args with
  | nil => simp [destThunk] at found
  | cons first rest =>
    cases rest with
    | cons second tail => cases first <;> simp [destThunk] at found
    | nil =>
      cases related with
      | cons head tail =>
        cases tail
        cases first <;> simp [destThunk] at found
        case refPtr flag key =>
          cases head
          exact ⟨flag, key, rfl, rfl⟩

/-- Successful force-body evaluation and its update are simulated after the
argument evaluation, with all force-body prerequisites derived from the
original state invariants. This is Flapjack induction infrastructure. -/
theorem forceUpdateAfterArguments {C F : Type} (c : Config)
    (xs : List ClosLang.Exp) (env : List Value)
    (initial middle : State (Spt ValApprox × C) F) (target : State C F)
    (args targetArgs : List Value) (value : Value) (forced : List Value)
    (final : State (Spt ValApprox × C) F) (sourceRefs : HolFiniteMapExact Nat (Ref Value))
    (runArgs : evaluate xs env initial = (.val args, middle))
    (states : StateRel c (nextG middle) middle target)
    (argsRelated : List.Forall₂ (ValueRel c (nextG middle)) args targetArgs)
    (found : destThunk args middle.refs = .isThunk .notEvaluated value)
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
    (ih : KnownSimulationAt [appUnit (.var .none 0)] [value] middle)
    (run : evaluate [appUnit (.var .none 0)] [value] middle = (.val forced, final))
    (update : updateThunk args final.refs forced = some sourceRefs) :
    ∃ other forced' targetFinal targetRefs,
      destThunk targetArgs target.refs = .isThunk .notEvaluated other ∧
      evaluate [appUnit (.var .none 0)] [other] target = (.val forced', targetFinal) ∧
      updateThunk targetArgs targetFinal.refs forced' = some targetRefs ∧
      List.Forall₂ (ValueRel c (nextG { final with refs := sourceRefs })) forced forced' ∧
      StateRel c (nextG { final with refs := sourceRefs })
        { final with refs := sourceRefs } { targetFinal with refs := targetRefs } ∧
      stateGlobalsApprox { final with refs := sourceRefs } (nextG { final with refs := sourceRefs }) ∧
      isStateOracle (compileInc c) ({ final with refs := sourceRefs }).compileOracle ∧
      oracleGapproxDisjoint (nextG { final with refs := sourceRefs })
        ({ final with refs := sourceRefs }).compileOracle := by
  obtain ⟨other, result', targetFinal, targetFound, targetRun, resultRelated,
    finalStates, finalGlobals, finalOracle, finalDisjoint⟩ :=
    forceBodyAfterArguments c xs env initial middle target args targetArgs value (.val forced) final
      runArgs states argsRelated found safe envSafe exprSafe oracleSyntax oracleSafe disjoint
      argsDisjoint argsUnique mono middleOracleDisjoint middleGlobals middleOracle ih run (by simp)
  cases result' with
  | err error => simp [resultRel] at resultRelated
  | val forced' =>
    have related : List.Forall₂ (ValueRel c (nextG final)) forced forced' := resultRelated
    obtain ⟨flag, key, rfl, rfl⟩ := relatedThunkPointers c (nextG middle) middle
      args targetArgs .notEvaluated value argsRelated found
    obtain ⟨targetRefs, targetUpdate, stateUpdate, globalsUpdate, oracleUpdate, disjointUpdate⟩ :=
      forcedUpdateSimulation c final targetFinal flag key forced forced' sourceRefs
        finalStates related finalGlobals finalOracle finalDisjoint update
    exact ⟨other, forced', targetFinal, targetRefs, targetFound, targetRun, targetUpdate,
      by simpa [nextG] using related, stateUpdate, globalsUpdate, oracleUpdate, disjointUpdate⟩

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Force
