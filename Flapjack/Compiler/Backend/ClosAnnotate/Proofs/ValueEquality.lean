module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.BlockLists

@[expose] public section

/-! Equality of values under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

mutual

/-- Structural equality gives the same result on two pairs of related values.
This candidate remains untagged pending HOL evaluator and carrier review. -/
theorem doEq_related (left right nextLeft nextRight : Value)
    (first : ValueRel left nextLeft) (second : ValueRel right nextRight) :
    doEq left right = doEq nextLeft nextRight := by
  cases first with
  | block tag fields nextFields related =>
    cases second with
    | block nextTag fields' nextFields' related' =>
      have len := related.length_eq
      have len' := related'.length_eq
      simp only [doEq, len, len']
      split
      · exact doEqList_related fields fields' nextFields nextFields' related related'
      · rfl
    | _ => simp [doEq]
  | _ => cases second <;> simp [doEq]
termination_by sizeOf left

/-- Elementwise-related lists have identical structural equality outcomes. -/
theorem doEqList_related (left right nextLeft nextRight : List Value)
    (first : List.Forall₂ ValueRel left nextLeft) (second : List.Forall₂ ValueRel right nextRight) :
    doEqList left right = doEqList nextLeft nextRight := by
  cases first with
  | nil => cases second <;> simp [doEqList]
  | cons head tail =>
    cases second with
    | nil => simp [doEqList]
    | cons head' tail' =>
      simp only [doEqList]
      rw [doEq_related _ _ _ _ head head']
      cases h : doEq _ _ with
      | typeError => rfl
      | val flag => cases flag <;> simp [doEqList_related _ _ _ _ tail tail']
termination_by sizeOf left

end

/-- The block equality primitive has identical results for related
arguments, including equality type errors. -/
theorem primitiveSimulation_equal {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.blockOp .equal) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil =>
    exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩
  | cons first rest =>
    cases rest with
    | nil =>
      exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩
    | cons second rest =>
      cases rest with
      | nil =>
        rename_i left nextLeft right nextRight
        have same := doEq_related left right nextLeft nextRight first second
        cases sourceEq : doEq left right with
        | typeError =>
          have targetEq : doEq nextLeft nextRight = .typeError := by rw [← same, sourceEq]
          exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock, targetEq], by
            simp [doApp, applyBlock, sourceEq, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩
        | val flag =>
          have targetEq : doEq nextLeft nextRight = .val flag := by rw [← same, sourceEq]
          refine ⟨.val (boolValue flag, target), ?_, ?_⟩
          · simp [doApp, applyBlock, targetEq]
          · simp only [doApp, applyBlock, sourceEq, AppResultRel]
            exact ⟨.block _ [] [] .nil, states⟩
      | cons third rest =>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩

/-- Constant comparisons produce related Boolean results or matching type
errors on related values. -/
theorem primitiveSimulation_equalConst {C F : Type} (part : ClosLang.ConstPart) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.equalConst part)) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil =>
    exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩
  | cons head tail =>
    cases tail with
    | nil =>
      cases head <;> cases part <;>
        simp [doApp, applyBlock, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel, states]
      all_goals exact .block _ [] [] .nil
    | cons first rest =>
      exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩

end Flapjack.Compiler.Backend.ClosAnnotate
