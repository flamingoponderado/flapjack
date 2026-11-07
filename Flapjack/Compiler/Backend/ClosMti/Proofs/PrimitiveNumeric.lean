import Flapjack.Compiler.Backend.ClosMti.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.Apply
import Flapjack.SemanticPrimitivesProps.ResultRelation

/-! Numeric primitive cases for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- Target-driven primitive simulation, including corresponding errors. This
is infrastructure for the closure evaluator's operation case. -/
def PrimitiveSimulation {C F : Type} (op : ClosLang.Op) : Prop :=
  ∀ (source target : State C F) (sourceValues targetValues : List Value),
    StateRel source target → List.Forall₂ (ValueRel source.maxApp) sourceValues targetValues →
    match (generalizing := false) doApp op targetValues target with
    | .err targetError => ∃ sourceError,
        doApp op sourceValues source = .err sourceError ∧
        excRel (ValueRel source.maxApp) sourceError targetError
    | .val (targetValue, targetFinal) => ∃ sourceValue sourceFinal,
        ValueRel source.maxApp sourceValue targetValue ∧ StateRel sourceFinal targetFinal ∧
        doApp op sourceValues source = .val (sourceValue, sourceFinal)

/-- Related arguments produce the same integer-primitive observation. -/
theorem doIntApp_related (maxApp : Nat) (op : ClosLang.IntOp) {left right : List Value}
    (related : List.Forall₂ (ValueRel maxApp) left right) :
    doIntApp op left = doIntApp op right := by
  cases op <;> cases related with
  | nil => rfl
  | cons head tail =>
    cases head <;> cases tail <;> simp_all [doIntApp]
    all_goals
      rename_i head2 tail2
      cases head2 <;> cases tail2 <;> simp_all

/-- Closure Boolean values relate to themselves. -/
theorem boolValue_related (maxApp : Nat) (value : Bool) :
    ValueRel maxApp (boolValue value) (boolValue value) := by
  cases value <;> exact .block _ [] [] .nil

/-- Successful integer primitives return numbers or Boolean values. -/
theorem doIntApp_result_related (maxApp : Nat) (op : ClosLang.IntOp) (args : List Value) (value : Value)
    (run : doIntApp op args = some value) : ValueRel maxApp value value := by
  cases op <;> cases args <;> simp_all [doIntApp]
  all_goals try (subst value; exact .number _)
  all_goals
    rename_i head tail
    cases head <;> cases tail <;> try simp_all
    all_goals try (obtain ⟨_, rfl⟩ := run; exact boolValue_related _ _)
    all_goals
      rename_i head2 tail2
      cases head2 <;> cases tail2 <;> try simp_all
      all_goals try (subst value; exact .number _)
      all_goals try (subst value; exact boolValue_related _ _)
      all_goals try (obtain ⟨_, rfl⟩ := run; exact .number _)

/-- Integer primitives preserve errors, related values, and related states. -/
theorem primitiveSimulation_int {C F : Type} (op : ClosLang.IntOp) :
    @PrimitiveSimulation C F (.intOp op) := by
  intro source target left right states values
  have same := doIntApp_related source.maxApp op values
  cases run : doIntApp op left with
  | none => simp [doApp, applyNumeric, ← same, run, excRel]
  | some value =>
    have valueRel := doIntApp_result_related source.maxApp op left value run
    simp [doApp, applyNumeric, ← same, run, valueRel, states]

/-- Related arguments produce the same word-primitive observation. -/
theorem doWordApp_related (maxApp : Nat) (op : ClosLang.WordOp) {left right : List Value}
    (related : List.Forall₂ (ValueRel maxApp) left right) :
    doWordApp op left = doWordApp op right := by
  cases op <;> cases related with
  | nil => rfl
  | cons head tail =>
    cases head <;> cases tail <;> simp_all [doWordApp, doWordAppIntegral]
    all_goals
      rename_i head2 tail2
      cases head2 <;> cases tail2 <;> try simp_all
      all_goals
        rename_i head3 tail3
        cases head3 <;> cases tail3 <;> simp_all

/-- Successful word primitives return scalar words, numbers, or Booleans. -/
theorem doWordApp_result_related (maxApp : Nat) (op : ClosLang.WordOp) (args : List Value) (value : Value)
    (run : doWordApp op args = some value) : ValueRel maxApp value value := by
  cases op <;> cases args <;> simp_all [doWordApp, doWordAppIntegral]
  all_goals
    rename_i head tail
    cases head <;> cases tail <;> try simp_all
    all_goals try (subst value; exact .word64 _)
    all_goals try (subst value; exact .number _)
    all_goals
      repeat
        first
        | split at run
        | simp_all
        | subst value
        | exact .number _
        | exact .word64 _
        | exact boolValue_related _ _
    all_goals try simp_all
    all_goals simp [intToByte] at run
    all_goals split at run <;> simp_all
    all_goals try (split at run <;> simp_all)
    all_goals try (subst value; exact .number _)
    all_goals try (subst value; exact .word64 _)

/-- Word primitives preserve errors, related values, and related states. -/
theorem primitiveSimulation_word {C F : Type} (op : ClosLang.WordOp) :
    @PrimitiveSimulation C F (.wordOp op) := by
  intro source target left right states values
  have same := doWordApp_related source.maxApp op values
  cases run : doWordApp op left with
  | none => simp [doApp, applyNumeric, ← same, run, excRel]
  | some value =>
    have valueRel := doWordApp_result_related source.maxApp op left value run
    simp [doApp, applyNumeric, ← same, run, valueRel, states]

end Flapjack.Compiler.Backend.ClosMti
