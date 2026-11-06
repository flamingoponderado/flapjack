import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationForce
import Flapjack.Compiler.Backend.ClosKnown.Proofs.Simulation
import Flapjack.Compiler.Backend.ClosKnown.Proofs.SourceEquations

/-! Forced-body induction for known-function optimization. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Force
open ClosSem ClosProps Relations Relations.StateRelation
open ClosProps.StateGlobalSafety BackendProps OracleGlobals OracleMonotonic UniqueGlobalsPort
open StateOracleDisjoint StateRelation.Oracle
open Flapjack.SemanticPrimitivesProps

/-- The optimizer leaves the forced thunk's generated application unchanged.
This is Flapjack induction infrastructure. -/
theorem knownForceBody (c : Config) (g : Spt ValApprox) :
    knownListTotal c [appUnit (.var .none 0)] [.other] g =
      ([(appUnit (.var .none 0), .other)], g) := by
  simp [appUnit, knownListTotal_app, knownListTotal_op, knownListTotal_var,
    knownListTotal, knownOpHOL, knownSourceHead, decideInlineHOL, ClosOp.smartOp, ClosOp.smartOp']

/-- Apply the original expression induction hypothesis to the thunk payload.
The state assumptions are the invariants at the point where the thunk is
forced; the expression, its environment, and its optimization are fixed by
the closure evaluator. This is Flapjack induction infrastructure. -/
theorem forceBodySimulation {C F : Type} (c : Config)
    (source : State (Spt ValApprox × C) F) (target : State C F)
    (value other : Value) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (final : State (Spt ValApprox × C) F)
    (states : StateRel c (nextG source) source target)
    (values : ValueRel c (nextG source) value other)
    (safe : ssgcFree source) (valueSafe : vsgcFree value)
    (oracleSyntax : coEveryFnVarsNone source.compileOracle)
    (oracleSafe : oracleStateSgcFree source.compileOracle)
    (disjoint : stateOracleMglobalsDisjoint source)
    (oracleDisjoint : oracleGapproxDisjoint (nextG source) source.compileOracle)
    (mono : oracleGapproxSubspt source.compileOracle)
    (unique : uniqueSetGlobals [] source.compileOracle)
    (globals : stateGlobalsApprox source (nextG source))
    (oracle : isStateOracle (compileInc c) source.compileOracle)
    (ih : KnownSimulationAt [appUnit (.var .none 0)] [value] source)
    (run : evaluate [appUnit (.var .none 0)] [value] source = (result, final))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ result' final',
      evaluate [appUnit (.var .none 0)] [other] target = (result', final') ∧
      resultRel (List.Forall₂ (ValueRel c (nextG final))) (ValueRel c (nextG final)) result result' ∧
      StateRel c (nextG final) final final' ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧
      oracleGapproxDisjoint (nextG final) final.compileOracle := by
  have treeSafe : globalsApproxSgcFree (nextG source) := by
    simpa [nextG, oracleStateSgcFree] using oracleSafe 0
  have refl : sptSubspt (nextG source) (nextG source) := by
    intro key member
    exact ⟨member, rfl⟩
  have exprSyntax : everyFnVarsNone [appUnit (.var .none 0)] := by
    simp [appUnit, everyFnVarsNone, fnVarsNoneExp]
  have exprSafe : ∀ e ∈ [appUnit (.var .none 0)], esgcFree e := by
    simp [appUnit, esgcFree, esgcFreeList]
  have exprDisjoint : mglobalsDisjoint source.globals [appUnit (.var .none 0)] := by
    simp [mglobalsDisjoint, appUnit, elistGlobals, setGlobals, opGlobalBag,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag]
  have exprUnique : uniqueSetGlobals [appUnit (.var .none 0)] source.compileOracle := by
    simpa [uniqueSetGlobals, appUnit, elistGlobals, setGlobals, opGlobalBag,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag] using unique
  have exprFv : fvMax 1 [appUnit (.var .none 0)] := by
    simp [fvMax, appUnit, freeVars, freeVarExp]
  have step := ih result final [value] [] [other] [] target c (nextG source) (nextG source)
    [.other] [(appUnit (.var .none 0), .other)]
    ⟨run, knownForceBody c (nextG source), states, exprSyntax, oracleSyntax, exprDisjoint,
      oracleDisjoint, disjoint, exprSafe, safe, by simpa using valueSafe,
      .cons (.other value) .nil, oracleSafe, treeSafe, by simp [valApproxSgcFree],
      globals, refl, refl, mono, exprFv, .cons values .nil, exprUnique, oracle, rfl, noType⟩
  simpa using step

/-- Related forced values can be stored at the original pointer while
preserving the final simulation invariants. This is Flapjack infrastructure
for the successful force case. -/
theorem forcedUpdateSimulation {C F : Type} (c : Config)
    (source : State (Spt ValApprox × C) F) (target : State C F)
    (flag : Bool) (key : Nat) (forced forced' : List Value)
    (sourceRefs : HolFiniteMapExact Nat (Ref Value))
    (states : StateRel c (nextG source) source target)
    (values : List.Forall₂ (ValueRel c (nextG source)) forced forced')
    (globals : stateGlobalsApprox source (nextG source))
    (oracle : isStateOracle (compileInc c) source.compileOracle)
    (oracleDisjoint : oracleGapproxDisjoint (nextG source) source.compileOracle)
    (updated : updateThunk [.refPtr flag key] source.refs forced = some sourceRefs) :
    ∃ targetRefs,
      updateThunk [.refPtr flag key] target.refs forced' = some targetRefs ∧
      StateRel c (nextG { source with refs := sourceRefs })
        { source with refs := sourceRefs } { target with refs := targetRefs } ∧
      stateGlobalsApprox { source with refs := sourceRefs } (nextG { source with refs := sourceRefs }) ∧
      isStateOracle (compileInc c) ({ source with refs := sourceRefs }).compileOracle ∧
      oracleGapproxDisjoint (nextG { source with refs := sourceRefs })
        ({ source with refs := sourceRefs }).compileOracle := by
  obtain ⟨targetRefs, targetRun, related⟩ :=
    relUpdateThunk c (nextG source) source target forced forced' flag key sourceRefs
      ⟨states, values⟩ updated
  exact ⟨targetRefs, targetRun, by simpa [nextG] using related,
    by simpa [nextG, stateGlobalsApprox] using globals, oracle,
    by simpa [nextG] using oracleDisjoint⟩

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Force
