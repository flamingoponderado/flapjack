module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationApplyFull
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.ClosureGlobals

@[expose] public section


/-! Full-application body induction for known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.ApplyFull
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint KnownUnchanged
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesProps

/-- The source body induction hypothesis can be invoked after a full closure
application. This derives its syntax, safety, approximation, clock, and oracle
conditions from the original application inputs. This is Flapjack induction
infrastructure for the full-application branch. -/
theorem fullApplicationBodySimulation {C F : Type} (c : Config)
    (source : State (Spt ValApprox × C) F) (target : State C F)
    (loc1 loc2 : Option Nat) (sourceFn targetFn : Value)
    (first : Value) (rest targetArgs : List Value) (argsopt : Option (List Value))
    (body : ClosLang.Exp) (bodyEnv remaining : List Value)
    (bodyResult : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (final : State (Spt ValApprox × C) F)
    (states : StateRel c (nextG source) source target)
    (fnRelated : valueRelApp c (nextG source) sourceFn targetFn argsopt)
    (argsRelated : List.Forall₂ (ValueRel c (nextG source)) (first :: rest) targetArgs)
    (locRelated : loptRel targetFn (first :: rest).length loc1 loc2)
    (constraint : argsopt.isSome → argsopt = some (first :: rest) ∧ (first :: rest) ≠ [] ∧ ∃ exp env,
      destClosure source.maxApp loc1 sourceFn (first :: rest) = some (.fullApp exp env []))
    (found : destClosure source.maxApp loc1 sourceFn (first :: rest) = some (.fullApp body bodyEnv remaining))
    (stateSafe : ssgcFree source) (fnSafe : vsgcFree sourceFn) (argsSafe : ∀ v ∈ first :: rest, vsgcFree v)
    (oracleSafe : oracleStateSgcFree source.compileOracle)
    (oracleSyntax : coEveryFnVarsNone source.compileOracle)
    (unique : uniqueSetGlobals [] source.compileOracle)
    (stateOracle : isStateOracle (compileInc c) source.compileOracle)
    (globals : stateGlobalsApprox source (nextG source))
    (oracleDisjoint : oracleGapproxDisjoint (nextG source) source.compileOracle)
    (disjoint : stateOracleMglobalsDisjoint source)
    (mono : oracleGapproxSubspt source.compileOracle)
    (ih : KnownSimulationAt [body] bodyEnv (decClock ((first :: rest).length - remaining.length) source))
    (run : evaluate [body] bodyEnv (decClock ((first :: rest).length - remaining.length) source) =
      (bodyResult, final)) (noType : bodyResult ≠ .err (.abort .typeError)) :
    ∃ targetBody targetEnv targetRemaining targetResult targetFinal,
      destClosure target.maxApp loc2 targetFn targetArgs = some (.fullApp targetBody targetEnv targetRemaining) ∧
      evaluate [targetBody] targetEnv (decClock (targetArgs.length - targetRemaining.length) target) =
        (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG final))) (ValueRel c (nextG final)) bodyResult targetResult ∧
      StateRel c (nextG final) final targetFinal ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧
      oracleGapproxDisjoint (nextG final) final.compileOracle ∧
      List.Forall₂ (ValueRel c (nextG source)) remaining targetRemaining ∧
      (loc1 ≠ loc2 → remaining = [] ∧ targetRemaining = []) := by
  obtain ⟨targetBody, sourcePrefix, sourceExtra, targetPrefix, targetExtra, targetRemaining, approxEnv,
    sourceEq, targetFound, prefixes, restRel, approxRel, bodyRel, fv, bodySyntax, annotation⟩ :=
    relatedFullApplication c (nextG source) source.maxApp loc1 loc2 sourceFn targetFn (first :: rest)
      targetArgs argsopt body bodyEnv remaining fnRelated argsRelated locRelated constraint found
  have safety := destClosureFullSgcFree source.maxApp loc1 sourceFn first rest body bodyEnv remaining
    ⟨found, fnSafe, argsSafe first (by simp), fun v hv => argsSafe v (by simp [hv])⟩
  have bodyEmpty : elistGlobals [body] = FlatProps.emptyGlobalBag := by
    funext key
    simp [elistGlobals, safety.1, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag]
  have bodySafe : ∀ e ∈ [body], esgcFree e := by simpa using setGlobalsEmptyEsgcFree body safety.1
  have bodyUnique : uniqueSetGlobals [body] source.compileOracle := by
    simpa [uniqueSetGlobals, elistGlobals_append, elistGlobals, safety.1, FlatProps.unionGlobalBag,
      FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using unique
  have bodyDisjoint : mglobalsDisjoint source.globals [body] := by
    simp [mglobalsDisjoint, bodyEmpty, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
  obtain ⟨g0, g1, bodyApprox, factor, sub, approxSafe, globalSafe, known⟩ := bodyRel
  have unchanged := knownUnchangedGlobals { c with inlineFactor := factor } [body] approxEnv
    g0 [(targetBody, bodyApprox)] g1 ⟨known, bodyEmpty⟩
  subst g1
  have reflSub : sptSubspt g0 g0 := by
    intro key member
    exact ⟨member, rfl⟩
  have maxEq : source.maxApp = target.maxApp := states.2.2.2.2.2.2.1
  have clockEq : source.clock = target.clock := states.2.2.2.2.1
  have costEq : (first :: rest).length - remaining.length = targetArgs.length - targetRemaining.length := by
    rw [argsRelated.length_eq, restRel.length_eq]
  let cost := (first :: rest).length - remaining.length
  have decStateBase : StateRel c (nextG (decClock cost source)) (decClock cost source) (decClock cost target) := by
    simpa [StateRel, decClock, nextG, clockEq] using states
  have decState : StateRel { c with inlineFactor := factor } (nextG (decClock cost source))
      (decClock cost source) (decClock cost target) := by
    simpa [stateRelUpdateInlineFactor] using decStateBase
  have inputRel : List.Forall₂ (ValueRel { c with inlineFactor := factor } (nextG (decClock cost source)))
      sourcePrefix targetPrefix := by
    simpa [decClock, nextG, valueRelUpdateInlineFactor] using prefixes
  have oracleDec : isStateOracle (compileInc { c with inlineFactor := factor })
      (decClock cost source).compileOracle := by
    simpa [decClock, compileIncUpdateInlineFactor] using stateOracle
  have step := ih bodyResult final sourcePrefix sourceExtra targetPrefix targetExtra (decClock cost target)
    { c with inlineFactor := factor } g0 g0 approxEnv [(targetBody, bodyApprox)]
    ⟨by simpa [cost, sourceEq] using run, known, decState, bodySyntax, by simpa [decClock] using oracleSyntax,
      by simpa [decClock] using bodyDisjoint, by simpa [decClock, nextG] using oracleDisjoint,
      by simpa [decClock, stateOracleMglobalsDisjoint] using disjoint, bodySafe,
      (ssgcFreeDecClock cost source).2 stateSafe, by simpa [sourceEq] using safety.2.1, approxRel,
      by simpa [decClock] using oracleSafe, globalSafe, approxSafe,
      by simpa [decClock, nextG, stateGlobalsApprox] using globals, reflSub,
      by simpa [decClock, nextG] using sub, by simpa [decClock] using mono, fv, inputRel,
      by simpa [decClock] using bodyUnique, oracleDec, sourceEq, noType⟩
  obtain ⟨targetResult, targetFinal, targetRun, resultRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := step
  refine ⟨targetBody, targetPrefix ++ targetExtra, targetRemaining, targetResult, targetFinal,
    by simpa [maxEq] using targetFound, ?_, ?_, ?_, finalGlobals, ?_, finalDisjoint, restRel, annotation⟩
  · simpa [cost, costEq] using targetRun
  · simpa [valueRelUpdateInlineFactor] using resultRel
  · simpa [stateRelUpdateInlineFactor] using finalState
  · simpa [compileIncUpdateInlineFactor] using finalOracle

/-- After a full closure body returns a value, the evaluator's recursive
application induction hypothesis applies to related remaining arguments.
This is Flapjack induction infrastructure for over-application. -/
theorem fullBodyContinuationSimulation {C F : Type} (c : Config)
    (source : State (Spt ValApprox × C) F) (targetFinal : State C F)
    (loc : Option Nat) (sourceFn : Value) (first : Value) (rest : List Value)
    (body : ClosLang.Exp) (bodyEnv remaining targetRemaining : List Value)
    (value targetValue : Value) (middle final : State (Spt ValApprox × C) F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (found : destClosure source.maxApp loc sourceFn (first :: rest) = some (.fullApp body bodyEnv remaining))
    (stateSafe : ssgcFree source) (fnSafe : vsgcFree sourceFn) (argsSafe : ∀ v ∈ first :: rest, vsgcFree v)
    (oracleSafe : oracleStateSgcFree source.compileOracle)
    (oracleSyntax : coEveryFnVarsNone source.compileOracle)
    (unique : uniqueSetGlobals [] source.compileOracle)
    (disjoint : stateOracleMglobalsDisjoint source) (mono : oracleGapproxSubspt source.compileOracle)
    (bodyRun : evaluate [body] bodyEnv (decClock ((first :: rest).length - remaining.length) source) =
      (.val [value], middle))
    (states : StateRel c (nextG middle) middle targetFinal)
    (valueRel : ValueRel c (nextG middle) value targetValue)
    (restRel : List.Forall₂ (ValueRel c (nextG source)) remaining targetRemaining)
    (globals : stateGlobalsApprox middle (nextG middle))
    (oracle : isStateOracle (compileInc c) middle.compileOracle)
    (oracleDisjoint : oracleGapproxDisjoint (nextG middle) middle.compileOracle)
    (ih : KnownAppSimulationAt loc value remaining middle)
    (run : evaluateApp loc value remaining middle = (result, final))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ targetResult targetLast,
      evaluateApp loc targetValue targetRemaining targetFinal = (targetResult, targetLast) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG final))) (ValueRel c (nextG final)) result targetResult ∧
      StateRel c (nextG final) final targetLast ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧ oracleGapproxDisjoint (nextG final) final.compileOracle := by
  let cost := (first :: rest).length - remaining.length
  let start := decClock cost source
  have closureSafety := destClosureFullSgcFree source.maxApp loc sourceFn first rest body bodyEnv remaining
    ⟨found, fnSafe, argsSafe first (by simp), fun v hv => argsSafe v (by simp [hv])⟩
  have bodyEmpty : elistGlobals [body] = FlatProps.emptyGlobalBag := by
    funext key
    simp [elistGlobals, closureSafety.1, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag]
  have bodySafe : ∀ e ∈ [body], esgcFree e := by
    simpa using setGlobalsEmptyEsgcFree body closureSafety.1
  have bodyUnique : uniqueSetGlobals [body] start.compileOracle := by
    simpa [start, decClock, uniqueSetGlobals, elistGlobals_append, elistGlobals, closureSafety.1,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using unique
  have bodyDisjoint : mglobalsDisjoint start.globals [body] := by
    simp [start, decClock, mglobalsDisjoint, bodyEmpty, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
  have startSafe : ssgcFree start := (ssgcFreeDecClock cost source).2 stateSafe
  have startDisjoint : stateOracleMglobalsDisjoint start := by
    simpa [start, decClock, stateOracleMglobalsDisjoint] using disjoint
  have bodyRun' : evaluate [body] bodyEnv start = (.val [value], middle) := by simpa [start, cost] using bodyRun
  have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals [body] bodyEnv start (.val [value]) middle
    ⟨bodyRun', startSafe, bodySafe, closureSafety.2.1⟩
  have valueSafe : vsgcFree value := by simpa [rsgcFree] using safety.2.1
  have nextDisjoint := stateOracleMglobalsDisjointEvaluate [body] bodyEnv start (.val [value]) middle
    ⟨bodyRun', startSafe, bodySafe, closureSafety.2.1, bodyUnique, bodyDisjoint, startDisjoint⟩
  obtain ⟨n, shifted⟩ := evaluateImpShiftSeq [body] bodyEnv start (.val [value]) middle bodyRun'
  have nextSyntax : coEveryFnVarsNone middle.compileOracle := by
    rw [shifted]
    exact coEveryFnVarsNoneShift start.compileOracle (by simpa [start, decClock] using oracleSyntax) n
  have nextSafe : oracleStateSgcFree middle.compileOracle := by
    rw [shifted]
    exact oracleStateSgcFreeShift start.compileOracle (by simpa [start, decClock] using oracleSafe) n
  have nextMono : oracleGapproxSubspt middle.compileOracle :=
    oracleGapproxSubsptEvaluate () [body] bodyEnv start (.val [value]) middle
      ⟨by simpa [start, decClock] using mono, bodyRun'⟩
  have nextUnique : uniqueSetGlobals [] middle.compileOracle :=
    uniqueSetGlobalsEvaluate [body] [] bodyEnv start middle (.val [value])
      ⟨by simpa [start, decClock] using unique, bodyRun'⟩
  have nextTree := nextGEvaluateSubspt [body] bodyEnv start (.val [value]) middle
    ⟨by simpa [start, decClock] using mono, bodyRun'⟩
  have remainingRel : List.Forall₂ (ValueRel c (nextG middle)) remaining targetRemaining := by
    have changed := valueRelListSubspt c (nextG start) remaining targetRemaining
      (by simpa [start, decClock, nextG] using restRel) (nextG middle) nextTree
    exact changed
  exact ih result final loc targetValue targetRemaining targetFinal c none
    ⟨run, by simpa [valueRelAppNone] using valueRel, oracleDisjoint, nextDisjoint, safety.1, valueSafe,
      closureSafety.2.2, nextSafe, nextSyntax, nextUnique, oracle, remainingRel, states, globals, nextMono,
      Or.inl rfl, by simp, noType⟩


end Flapjack.Compiler.Backend.ClosKnown.Simulation.ApplyFull
