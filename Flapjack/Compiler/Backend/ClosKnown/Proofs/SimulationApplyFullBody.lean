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

/-- The non-timeout full-application branch satisfies the original
application simulation using its body and continuation induction hypotheses.
This is Flapjack induction infrastructure for the full application case. -/
theorem fullApplicationBodyCase {C F : Type} (loc1 : Option Nat) (sourceFn : Value)
    (first : Value) (rest : List Value) (s0 : State (Spt ValApprox × C) F)
    (body : ClosLang.Exp) (env remaining : List Value)
    (found : destClosure s0.maxApp loc1 sourceFn (first :: rest) = some (.fullApp body env remaining))
    (enough : ¬ s0.clock < (first :: rest).length - remaining.length)
    (bodyIH : KnownSimulationAt [body] env (decClock ((first :: rest).length - remaining.length) s0))
    (appIH : ∀ value middle,
      evaluate [body] env (decClock ((first :: rest).length - remaining.length) s0) = (.val [value], middle) →
      KnownAppSimulationAt loc1 value remaining middle) :
    KnownAppSimulationAt loc1 sourceFn (first :: rest) s0 := by
  intro res1 s loc2 targetFn targetArgs t0 c argsopt h
  obtain ⟨run, fnRel, oracleDisjoint, disjoint, stateSafe, fnSafe, argsSafe, oracleSafe, oracleSyntax,
    unique, oracle, argsRel, states, globals, mono, locRel, constraint, noType⟩ := h
  have targetNonempty : targetArgs ≠ [] := by
    intro eq
    subst targetArgs
    cases argsRel
  cases targetArgs with
  | nil => contradiction
  | cons targetFirst targetRest =>
    have clockEq : s0.clock = t0.clock := states.2.2.2.2.1
    rw [evaluateApp, found] at run
    simp only [enough, ↓reduceIte, fixClock_evaluate] at run
    cases bodyRun : evaluate [body] env (decClock ((first :: rest).length - remaining.length) s0) with
    | mk bodyResult middle =>
      rw [bodyRun] at run
      cases bodyResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨targetBody, targetEnv, targetRemaining, targetResult, targetMiddle, targetFound,
          targetBodyRun, related, finalState, finalGlobals, finalOracle, finalDisjoint, restRel, annotation⟩ :=
          fullApplicationBodySimulation c s0 t0 loc1 loc2 sourceFn targetFn first rest (targetFirst :: targetRest)
            argsopt body env remaining (.err error) middle states fnRel argsRel locRel constraint found
            stateSafe fnSafe argsSafe oracleSafe oracleSyntax unique oracle globals oracleDisjoint disjoint mono
            bodyIH bodyRun noType
        cases targetResult with
        | val values => simp [resultRel] at related
        | err targetError =>
          have targetEnough : ¬ t0.clock < (targetFirst :: targetRest).length - targetRemaining.length := by
            have a := argsRel.length_eq
            have b := restRel.length_eq
            omega
          refine ⟨.err targetError, targetMiddle, ?_, related, finalState, finalGlobals, finalOracle, finalDisjoint⟩
          rw [evaluateApp, targetFound]
          dsimp only
          rw [if_neg targetEnough, fixClock_evaluate, targetBodyRun]
      | val values =>
        have singleton := evaluate_singleton_value body env
          (decClock ((first :: rest).length - remaining.length) s0) middle values bodyRun
        obtain ⟨value, rfl⟩ := singleton
        dsimp only at run
        obtain ⟨targetBody, targetEnv, targetRemaining, targetResult, targetMiddle, targetFound,
          targetBodyRun, related, midState, midGlobals, midOracle, midDisjoint, restRel, annotation⟩ :=
          fullApplicationBodySimulation c s0 t0 loc1 loc2 sourceFn targetFn first rest (targetFirst :: targetRest)
            argsopt body env remaining (.val [value]) middle states fnRel argsRel locRel constraint found
            stateSafe fnSafe argsSafe oracleSafe oracleSyntax unique oracle globals oracleDisjoint disjoint mono
            bodyIH bodyRun (by simp)
        cases targetResult with
        | err error => simp [resultRel] at related
        | val values2 =>
          cases related with
          | cons valueRel tail =>
            cases tail
            rename_i targetValue
            have targetEnough : ¬ t0.clock < (targetFirst :: targetRest).length - targetRemaining.length := by
              have a := argsRel.length_eq
              have b := restRel.length_eq
              omega
            by_cases same : loc1 = loc2
            · subst loc2
              obtain ⟨targetResult, targetLast, continuation, resultRelated, finalState, finalGlobals,
                finalOracle, finalDisjoint⟩ :=
                fullBodyContinuationSimulation c s0 targetMiddle loc1 sourceFn first rest body env remaining
                  targetRemaining value targetValue middle s res1 found stateSafe fnSafe argsSafe oracleSafe
                  oracleSyntax unique disjoint mono bodyRun midState valueRel restRel midGlobals midOracle
                  midDisjoint (appIH value middle bodyRun) run noType
              refine ⟨targetResult, targetLast, ?_, resultRelated, finalState, finalGlobals, finalOracle, finalDisjoint⟩
              rw [evaluateApp, targetFound]
              dsimp only
              rw [if_neg targetEnough, fixClock_evaluate, targetBodyRun]
              exact continuation
            · obtain ⟨sourceEmpty, targetEmpty⟩ := annotation same
              subst remaining
              subst targetRemaining
              simp [evaluateApp] at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨.val [targetValue], targetMiddle, ?_, .cons valueRel .nil, midState, midGlobals, midOracle, midDisjoint⟩
              rw [evaluateApp, targetFound]
              dsimp only
              rw [if_neg targetEnough, fixClock_evaluate, targetBodyRun]
              simp [evaluateApp]

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Nonempty application case of the original optimizer simulation, retaining
the evaluator's body and continuation induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0AppCons {C F : Type} (loc : Option Nat) (function first : Value)
    (rest : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (appIH : ∀ (kind : AppKind) (body : ClosLang.Exp) (env remaining : List Value)
      (bodyResult : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
      (middle : ClosSem.State (Spt ValApprox × C) F) (values : List Value) (value : Value) (tail : List Value),
      destClosure s0.maxApp loc function (first :: rest) = some kind ∧
      kind = .fullApp body env remaining ∧
      ¬ (s0.clock < (first :: rest).length - remaining.length) ∧
      evaluate [body] env (decClock ((first :: rest).length - remaining.length) s0) = (bodyResult, middle) ∧
      bodyResult = .val values ∧ values = value :: tail ∧ tail = [] →
      KnownAppSimulationAt loc value remaining middle)
    (bodyIH : ∀ (kind : AppKind) (body : ClosLang.Exp) (env remaining : List Value),
      destClosure s0.maxApp loc function (first :: rest) = some kind ∧
      kind = .fullApp body env remaining ∧
      ¬ (s0.clock < (first :: rest).length - remaining.length) →
      KnownSimulationAt [body] env (decClock ((first :: rest).length - remaining.length) s0)) :
    KnownAppSimulationAt loc function (first :: rest) s0 := by
  cases found : destClosure s0.maxApp loc function (first :: rest) with
  | none =>
    intro res1 s loc2 f2 args2 t0 c argsopt h
    obtain ⟨run, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, noType⟩ := h
    rw [evaluateApp, found] at run
    simp at run
    rcases run with ⟨rfl, rfl⟩
    exact (noType rfl).elim
  | some kind =>
    cases kind with
    | partialApp value => exact ApplyPartial.knownAppPartialCase loc function first rest s0 value found
    | fullApp body env remaining =>
      by_cases timeout : s0.clock < (first :: rest).length - remaining.length
      · exact fullApplicationTimeoutCase loc function first rest s0 body env remaining found timeout
      · apply fullApplicationBodyCase loc function first rest s0 body env remaining found timeout
        · exact bodyIH (.fullApp body env remaining) body env remaining ⟨found, rfl, timeout⟩
        · intro value middle run
          exact appIH (.fullApp body env remaining) body env remaining (.val [value]) middle
            [value] value [] ⟨found, rfl, timeout, run, rfl, rfl, rfl⟩

end Flapjack.Compiler.Backend.ClosKnown.Simulation.ApplyFull
