module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.InlineFreeVars
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.KnownUnchanged
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationAppPrefix
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.TicksEvaluate

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


/-! Constructing the synthetic target closure for an inlined application. -/
namespace Flapjack.Compiler.Backend.ClosKnown.InlineClosureRelation
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps Relations KnownUnchanged
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint
open Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The optimized inline body forms a related synthetic closure. Its target
capture may be any environment because closedness ensures that the body only
uses the supplied arguments. This is Flapjack induction infrastructure. -/
theorem inlineBodyClosureRel (c : Config) (g current after : Spt ValApprox)
    (approx : ValApprox) (loc : Option Nat) (arity address : Nat)
    (body targetBody : ClosLang.Exp)
    (captures targetCaptures args : List ClosSem.Value) (argApproxs : List ValApprox)
    (bodyApprox : ValApprox) (relatedFn : ClosSem.Value)
    (decision : decideInlineHOL c approx loc arity = .letInline body)
    (sourceRelated : ValueRel c current (.closure (some address) [] captures arity body) relatedFn)
    (approxSafe : valApproxSgcFree approx)
    (argsSafe : ∀ a ∈ argApproxs, valApproxSgcFree a)
    (argsApprox : List.Forall₂ ValApproxVal argApproxs args)
    (globalsSafe : globalsApproxSgcFree g)
    (known : knownListTotal (decInlineFactor c) [body] argApproxs g = ([(targetBody, bodyApprox)], after))
    (sub : sptSubspt g current) :
    valueRelApp c current (.closure (some address) [] captures arity body)
      (.closure (some address) [] targetCaptures arity targetBody) (some args) := by
  have free := (InlineFreeVars.decideInlineLetInlineFvMax c approx loc arity body decision).choose_spec.choose_spec.2
  have bodySyntax : everyFnVarsNone [body] := (valueRelClosure c current (some address) [] captures arity body relatedFn).mp sourceRelated |>.1
  have unchanged := inlineBodyGlobalsUnchanged c approx loc arity body argApproxs g
    [(targetBody, bodyApprox)] after approxSafe decision known
  subst after
  have bodyRel : expRel c argApproxs current body targetBody := by
    refine ⟨g, g, bodyApprox, (decInlineFactor c).inlineFactor, sub, argsSafe, globalsSafe, ?_⟩
    simpa [decInlineFactor] using known
  simp only [valueRelApp]
  refine ⟨bodySyntax, [], [], captures, [], [], targetCaptures, targetBody, argApproxs,
    rfl, ?_, .nil, .nil, .nil, ⟨argsApprox, trivial⟩, ?_, rfl⟩
  · simpa using free
  · simpa using bodyRel

/-- The source application induction hypothesis simulates a selected inline
body, with the target closure call expressed as the generated ticks. This
includes clock exhaustion and every non-type-error result. It is Flapjack
infrastructure for the inlining case. -/
theorem inlineApplicationContinuation {C F : Type} (c : Config)
    (trace : BackendCommon.Tra) (loc : Option Nat) (arity : Nat)
    (approx : ValApprox) (body targetBody : ClosLang.Exp) (bodyApprox : ValApprox)
    (g after : Spt ValApprox) (argApproxs : List ValApprox)
    (fn relatedFn : ClosSem.Value) (args targetArgs targetCaptures : List ClosSem.Value)
    (source : State (Spt ValApprox × C) F) (target : State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value) (final : State (Spt ValApprox × C) F)
    (ih : Simulation.KnownAppSimulationAt loc fn args source)
    (decision : decideInlineHOL c approx loc arity = .letInline body)
    (fnApprox : ValApproxVal approx fn)
    (argsApprox : List.Forall₂ ValApproxVal argApproxs args)
    (argApproxSafe : ∀ a ∈ argApproxs, valApproxSgcFree a)
    (approxSafe : valApproxSgcFree approx) (globalsSafe : globalsApproxSgcFree g)
    (known : knownListTotal (decInlineFactor c) [body] argApproxs g = ([(targetBody, bodyApprox)], after))
    (sub : sptSubspt g (nextG source))
    (arityEq : arity = args.length) (nonempty : args ≠ [])
    (h : List.Forall₂ (ValueRel c (nextG source)) args targetArgs ∧
      ValueRel c (nextG source) fn relatedFn ∧
      ssgcFree source ∧ vsgcFree fn ∧ (∀ v ∈ args, vsgcFree v) ∧
      oracleStateSgcFree source.compileOracle ∧ coEveryFnVarsNone source.compileOracle ∧
      uniqueSetGlobals [] source.compileOracle ∧ stateOracleMglobalsDisjoint source ∧
      oracleGapproxSubspt source.compileOracle ∧ StateRel c (nextG source) source target ∧
      stateGlobalsApprox source (nextG source) ∧ isStateOracle (compileInc c) source.compileOracle ∧
      oracleGapproxDisjoint (nextG source) source.compileOracle)
    (run : evaluateApp loc fn args source = (result, final))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ targetResult targetFinal,
      evaluate [ticks trace 1 arity targetBody] (targetArgs ++ targetCaptures) target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG final))) (ValueRel c (nextG final)) result targetResult ∧
      StateRel c (nextG final) final targetFinal ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧
      oracleGapproxDisjoint (nextG final) final.compileOracle := by
  obtain ⟨address, size, approxEq⟩ := decideInlineLetInlineImpClos c approx loc arity body decision
  have locNone : loc = none := by
    cases loc <;> simp_all [decideInlineHOL]
  subst loc
  have closureApprox : ValApproxVal (.clos address arity body size) fn := by simpa [approxEq] using fnApprox
  cases closureApprox with
  | clos _ _ _ _ captures =>
    obtain ⟨argsRel, fnRel, safe, fnSafe, argsSafe, oracleSafe, coSyntax, unique,
      disjoint, mono, state, globals, stateOracle, oracle⟩ := h
    have closureRel := inlineBodyClosureRel c g (nextG source) after approx none arity address body targetBody
      captures targetCaptures args argApproxs bodyApprox relatedFn decision fnRel approxSafe argApproxSafe
      argsApprox globalsSafe known sub
    have enough : args.length ≤ source.maxApp := by
      by_contra bad
      have dest : destClosure source.maxApp none (.closure (some address) [] captures arity body) args = none := by
        simp [destClosure, checkLoc, bad]
      cases args with
      | nil => contradiction
      | cons first rest =>
        rw [evaluateApp, dest] at run
        cases run
        exact noType rfl
    have positive : 0 < args.length := List.length_pos_iff.mpr nonempty
    have takeAll : args.reverse.take args.length = args.reverse := by
      simpa only [List.length_reverse] using
        (show args.reverse.take args.reverse.length = args.reverse from List.take_length)
    have dest : destClosure source.maxApp none (.closure (some address) [] captures arity body) args =
        some (.fullApp body (args ++ captures) []) := by
      simp [destClosure, checkLoc, enough, arityEq, positive, takeAll]
    have location : loptRel (.closure (some address) [] targetCaptures arity targetBody)
        args.length none (some address) := by
      simp [loptRel, arityEq]
    have targetNonempty : targetArgs ≠ [] := by
      intro eq
      have lengths := argsRel.length_eq
      simp [eq] at lengths
      exact nonempty lengths
    obtain ⟨targetResult, targetFinal, targetRun, resultRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩ :=
      ih result final (some address) (.closure (some address) [] targetCaptures arity targetBody)
        targetArgs target c (some args)
        ⟨run, closureRel, oracle, disjoint, safe, fnSafe, argsSafe, oracleSafe, coSyntax, unique,
          stateOracle, argsRel, state, globals, mono, location,
          by intro _; exact ⟨rfl, nonempty, body, args ++ captures, dest⟩, noType⟩
    refine ⟨targetResult, targetFinal, ?_, resultRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩
    have lengths := argsRel.length_eq
    have targetEq := TicksEvaluate.exactApplicationEqTicks trace 1 address targetArgs targetCaptures targetBody target targetNonempty
    rw [← lengths, ← arityEq] at targetEq
    rw [← targetEq]
    simpa [arityEq, lengths] using targetRun

end Flapjack.Compiler.Backend.ClosKnown.InlineClosureRelation
