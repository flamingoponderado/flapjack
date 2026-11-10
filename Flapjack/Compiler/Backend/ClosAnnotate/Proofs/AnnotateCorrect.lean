module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Evaluate
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.StateRelation.Original

@[expose] public section

/-! Initial-program consequences of the candidate annotation simulation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL (Result)

namespace AnnotateCorrectPort
/-- The closure state uses canonical finite-support maps. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end AnnotateCorrectPort

/-- The annotation simulation at an empty source environment. The code
predicate renders HOL's `FEVERY` using successful finite-map lookups. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "annotate_correct"
  (nested_list_rel_as_mutual := [FunctionsRel]) (fmap_as_finite_support := [refs, code])]
theorem annotate_correct {C F : Type} (program : List ClosLang.Exp) (source : State C F)
    (result : Result (List Value) Value) (next target : State C F) (targetEnv : List Value)
    (hypotheses : evaluate program [] source = (result, next) ∧
      result ≠ .err (.abort .typeError) ∧ everyFnVarsNone program ∧
      (∀ key entry, source.code.lookup key = some entry → everyFnVarsNone [entry.2]) ∧
      (∀ index, everyFnVarsNone (source.compileOracle index).2.1 ∧
        everyFnVarsNone ((source.compileOracle index).2.2.map (fun (_, _, body) => body))) ∧
      StateRelSource source target) :
    ∃ targetResult targetNext, evaluate (annotateSource 0 program) targetEnv target = (targetResult, targetNext) ∧
      Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel result targetResult ∧
      StateRelSource next targetNext := by
  obtain ⟨run, noType, safe, code, oracle, states⟩ := hypotheses
  have codeSafe : CodeSafe source := by
    intro key arity body found
    exact code key (arity, body) found
  have vars : ∀ n, altFv n program = true → EnvOk 0 0 .ln [] targetEnv n := by
    exact envSetDefault {n | altFv n program = true} targetEnv
  obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
    evaluate_simulation.1 program [] source targetEnv target result next 0 0 .ln run noType (by simp)
      vars safe codeSafe oracle ((stateRelSource_iff source target).mp states)
  refine ⟨targetResult, targetNext, ?_, resultRel, (stateRelSource_iff next targetNext).mpr nextRel⟩
  simpa [annotateSource, altFreeSource_eq_altFree, shiftSource_eq_shiftList] using targetRun

/-- The mutual expression and application simulation, with the source
finite-map `FEVERY` clauses rendered by successful lookups. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "shift_correct"
  (nested_list_rel_as_mutual := [FunctionsRel]) (fmap_as_finite_support := [refs, code])]
theorem shift_correct {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List Value) (source : State C F)
      (targetEnv : List Value) (target : State C F) (result : Result (List Value) Value)
      (next : State C F) (m l : Nat) (index : Spt Nat),
      (evaluate expressions env source = (result, next) ∧
        result ≠ .err (.abort .typeError) ∧ env.length = m + l ∧
        {n | altFvSource n expressions = true} ⊆ {n | EnvOk m l index env targetEnv n} ∧
        everyFnVarsNone expressions ∧
        (∀ key entry, source.code.lookup key = some entry → everyFnVarsNone [entry.2]) ∧
        (∀ n, everyFnVarsNone (source.compileOracle n).2.1 ∧
          everyFnVarsNone ((source.compileOracle n).2.2.map (fun (_, _, body) => body))) ∧
        StateRelSource source target) →
      ∃ targetResult targetNext,
        evaluate (shiftSource (altFreeSource expressions).1 m l index) targetEnv target =
          (targetResult, targetNext) ∧
        Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel result targetResult ∧
        StateRelSource next targetNext) ∧
    (∀ (location : Option Nat) (function : Value) (args : List Value) (source : State C F)
      (result : Result (List Value) Value) (next : State C F) (targetFunction : Value)
      (targetArgs : List Value) (target : State C F),
      (evaluateApp location function args source = (result, next) ∧
        ValueRel function targetFunction ∧ List.Forall₂ ValueRel args targetArgs ∧
        (∀ key entry, source.code.lookup key = some entry → everyFnVarsNone [entry.2]) ∧
        (∀ n, everyFnVarsNone (source.compileOracle n).2.1 ∧
          everyFnVarsNone ((source.compileOracle n).2.2.map (fun (_, _, body) => body))) ∧
        StateRelSource source target ∧ result ≠ .err (.abort .typeError)) →
      ∃ targetResult targetNext,
        evaluateApp location targetFunction targetArgs target = (targetResult, targetNext) ∧
        Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel result targetResult ∧
        StateRelSource next targetNext) := by
  constructor
  · intro expressions env source targetEnv target result next m l index h
    obtain ⟨run, noType, length, vars, safe, code, oracle, states⟩ := h
    have codeSafe : CodeSafe source := by
      intro key arity body found
      exact code key (arity, body) found
    have varsSafe : ∀ n, altFv n expressions = true → EnvOk m l index env targetEnv n := by
      intro n present
      apply vars
      simpa [altFvSource_eq_altFv] using present
    obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
      evaluate_simulation.1 expressions env source targetEnv target result next m l index
        run noType length varsSafe safe codeSafe oracle ((stateRelSource_iff source target).mp states)
    refine ⟨targetResult, targetNext, ?_, resultRel, (stateRelSource_iff next targetNext).mpr nextRel⟩
    simpa [altFreeSource_eq_altFree, shiftSource_eq_shiftList] using targetRun
  · intro location function args source result next targetFunction targetArgs target h
    obtain ⟨run, functionRel, argsRel, code, oracle, states, noType⟩ := h
    have codeSafe : CodeSafe source := by
      intro key arity body found
      exact code key (arity, body) found
    obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
      evaluate_simulation.2 (source.clock + 1) location function targetFunction args targetArgs
        source target result next (by omega) run noType functionRel argsRel codeSafe oracle
        ((stateRelSource_iff source target).mp states)
    exact ⟨targetResult, targetNext, targetRun, resultRel, (stateRelSource_iff next targetNext).mpr nextRel⟩

end Flapjack.Compiler.Backend.ClosAnnotate
