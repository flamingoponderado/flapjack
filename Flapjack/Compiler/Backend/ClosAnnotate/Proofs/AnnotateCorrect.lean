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

end Flapjack.Compiler.Backend.ClosAnnotate
