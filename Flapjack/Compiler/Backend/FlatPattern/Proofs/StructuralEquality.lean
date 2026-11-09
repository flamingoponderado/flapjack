import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveComparison
import Flapjack.Compiler.Backend.FlatProps.SimpleEquality

/-! Structural equality for the proof-side flat pattern relations. The flat
evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend

/-- General equality preserves successful primitive results for related values. -/
theorem doApp_equality_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : SemanticPrimitivesHOL.Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .equality) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .equality) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ SemanticPrimitivesProps.resultRel ValueRel ValueRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
  | @cons first first' tail tail' firstRel rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
    | @cons second second' tail tail' secondRel rest =>
      cases rest with
      | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
      | nil =>
        have equality := FlatProps.doEq_simple ValueRel simpleValueRel_valueRel first second first' second' firstRel secondRel
        cases compared : FlatSem.doEq first second with
        | typeError => simp [FlatSem.doApp, FlatSem.doAppNumeric, compared] at run
        | val boolean =>
          have compared' : FlatSem.doEq first' second' = .val boolean := by rw [← equality, compared]
          simp [FlatSem.doApp, FlatSem.doAppNumeric, compared] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨target, .val (FlatSem.boolValue boolean), by simp [FlatSem.doApp, FlatSem.doAppNumeric, compared'],
            states, (boolValue_related boolean)⟩

end Flapjack.Compiler.Backend.FlatPattern
