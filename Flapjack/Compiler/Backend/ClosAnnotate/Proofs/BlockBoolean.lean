module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.BlockInspection
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Control

@[expose] public section

/-! Boolean and bounds operations under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Negating a Boolean has the same result or type error on related values. -/
theorem primitiveSimulation_boolNot {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.blockOp .boolNot) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil =>
    exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩
  | cons head tail =>
    cases tail with
    | nil =>
      rename_i value nextValue
      have same := valueRel_asBool head
      cases observed : asBool value with
      | none =>
        have nextObserved : asBool nextValue = none := by rw [← same, observed]
        exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock, nextObserved], by
          simp [doApp, applyBlock, observed, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩
      | some flag =>
        have nextObserved : asBool nextValue = some flag := by rw [← same, observed]
        refine ⟨.val (boolValue (!flag), target), ?_, ?_⟩
        · simp [doApp, applyBlock, nextObserved]
        · simp only [doApp, applyBlock, observed, AppResultRel]
          exact ⟨.block _ [] [] .nil, states⟩
    | cons first rest =>
      exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩

/-- Boolean tests preserve observations and reject the same malformed inputs. -/
theorem primitiveSimulation_boolTest {C F : Type} (test : Flapjack.AstHOL.Test) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.boolTest test)) := by
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
        have firstSame := valueRel_asBool first
        have secondSame := valueRel_asBool second
        cases firstObserved : asBool left with
        | none =>
          have nextFirst : asBool nextLeft = none := by rw [← firstSame, firstObserved]
          exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock, nextFirst], by
            simp [doApp, applyBlock, firstObserved, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩
        | some a =>
          have nextFirst : asBool nextLeft = some a := by rw [← firstSame, firstObserved]
          cases secondObserved : asBool right with
          | none =>
            have nextSecond : asBool nextRight = none := by rw [← secondSame, secondObserved]
            exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock, nextFirst, nextSecond], by
              simp [doApp, applyBlock, firstObserved, secondObserved, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩
          | some b =>
            have nextSecond : asBool nextRight = some b := by rw [← secondSame, secondObserved]
            refine ⟨.val (boolValue (a == b), target), ?_, ?_⟩
            · simp [doApp, applyBlock, nextFirst, nextSecond]
            · simp only [doApp, applyBlock, firstObserved, secondObserved, AppResultRel]
              exact ⟨.block _ [] [] .nil, states⟩
      | cons third rest =>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩

/-- Block bounds checks agree because related blocks have equal lengths. -/
theorem primitiveSimulation_boundsCheckBlock {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.blockOp .boundsCheckBlock) := by
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
        cases first with
        | block tag fields nextFields fieldsRel =>
          cases second with
          | number index =>
            let result := boolValue (decide (0 ≤ index ∧ index < Int.ofNat fields.length))
            have sameLength := fieldsRel.length_eq
            refine ⟨.val (result, target), ?_, ?_⟩
            · simp [doApp, applyBlock, result, ← sameLength]
            · simp only [doApp, applyBlock, AppResultRel]
              exact ⟨.block _ [] [] .nil, states⟩
          | _ =>
            exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩
        | _ =>
          cases second <;>
            exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩
      | cons third rest =>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩

/-- A constant translates to a value related to itself, including nested
constructor constants. -/
theorem makeConst_related (constant : ClosLang.Const) : ValueRel (makeConst constant) (makeConst constant) := by
  cases constant with
  | constInt value => simpa [makeConst] using ValueRel.number value
  | constWord64 value => simpa [makeConst] using ValueRel.word64 value
  | constStr value => simpa [makeConst] using ValueRel.byteVector _
  | constCons tag fields =>
    simp only [makeConst]
    apply ValueRel.block
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro first member
    exact makeConst_related first
termination_by sizeOf constant
decreasing_by have h := List.sizeOf_lt_of_mem member; simp_wf; omega

/-- Constant construction preserves the candidate primitive relation. -/
theorem primitiveSimulation_constant {C F : Type} (constant : ClosLang.Const) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.constant constant)) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil =>
    refine ⟨.val (makeConst constant, target), ?_, ?_⟩
    · simp [doApp, applyBlock]
    · simpa [doApp, applyBlock, AppResultRel] using And.intro (makeConst_related constant) states
  | cons head tail =>
    exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]⟩

end Flapjack.Compiler.Backend.ClosAnnotate
