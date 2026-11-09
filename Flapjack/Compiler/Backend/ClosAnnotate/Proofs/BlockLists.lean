import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.BlockInspection

/-! List-valued block operations under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Related lists encode to related closure-language list values. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "list_to_v_v_rel"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem listToValue_related (left right : List Value) (related : List.Forall₂ ValueRel left right) :
    ValueRel (listToValue left) (listToValue right) := by
  induction related with
  | nil => exact .block _ [] [] .nil
  | cons head tail ih => exact .block _ _ _ (.cons head (.cons ih .nil))

/-- This option-relation reformulation is Flapjack infrastructure for the
recursive proof and its consumers; the HOL disjunction is stated below. -/
theorem valueToList_related (left right : Value) (related : ValueRel left right) :
    optionRel (List.Forall₂ ValueRel) (valueToList left) (valueToList right) := by
  cases related with
  | block tag leftFields rightFields fields =>
    cases fields with
    | nil =>
      by_cases nil : tag = BackendCommon.nilTag
      · simp [valueToList, nil, optionRel]
      · simp [valueToList, nil, optionRel]
    | cons first rest =>
      cases rest with
      | nil => simp [valueToList, optionRel]
      | cons tail rest =>
        cases rest with
        | nil =>
          by_cases cons : tag = BackendCommon.consTag
          · simp only [valueToList, cons, ↓reduceIte]
            have tails := valueToList_related _ _ tail
            cases leftTail : valueToList _ with
            | none =>
              cases rightTail : valueToList _ <;> simp [leftTail, rightTail, optionRel] at tails ⊢
            | some xs =>
              cases rightTail : valueToList _ with
              | none => simp [leftTail, rightTail, optionRel] at tails
              | some ys =>
                simp only [leftTail, rightTail, Option.map, optionRel] at tails ⊢
                exact .cons first tails
          · simp [valueToList, cons, optionRel]
        | cons third rest => simp [valueToList, optionRel]
  | _ => simp [valueToList, optionRel]
termination_by sizeOf left
decreasing_by simp_wf; omega

/-- Related values decode either to two failures or to related lists. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "v_to_list"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem valueToList_relation (left right : Value) (related : ValueRel left right) :
    (valueToList left = none ∧ valueToList right = none) ∨
      ∃ xs ys, valueToList left = some xs ∧ valueToList right = some ys ∧
        List.Forall₂ ValueRel xs ys := by
  have decoded := valueToList_related left right related
  cases leftRun : valueToList left with
  | none =>
    cases rightRun : valueToList right <;> simp_all [optionRel]
  | some xs =>
    cases rightRun : valueToList right <;> simp_all [optionRel]

/-- Converting a closure-language list into a tagged block preserves its
fields and agrees on malformed inputs. -/
theorem primitiveSimulation_fromList {C F : Type} (tag : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.fromList tag)) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil =>
    exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel]⟩
  | cons head tail =>
    cases tail with
    | nil =>
      rename_i left right
      have decoded := valueToList_related left right head
      cases leftRun : valueToList left with
      | none =>
        cases rightRun : valueToList right with
        | none =>
          exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock, rightRun], by
            simp [doApp, applyBlock, leftRun, AppResultRel, ResultRel]⟩
        | some ys => simp [leftRun, rightRun, optionRel] at decoded
      | some xs =>
        cases rightRun : valueToList right with
        | none => simp [leftRun, rightRun, optionRel] at decoded
        | some ys =>
          have fields : List.Forall₂ ValueRel xs ys := by simpa [leftRun, rightRun, optionRel] using decoded
          refine ⟨.val (.block tag ys, target), ?_, ?_⟩
          · simp [doApp, applyBlock, rightRun]
          · simpa [doApp, applyBlock, leftRun, AppResultRel] using And.intro (ValueRel.block tag xs ys fields) states
    | cons first rest =>
      exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel]⟩

/-- Appending two encoded lists preserves their related elements and agrees
on decoding failures. -/
theorem primitiveSimulation_listAppend {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.blockOp .listAppend) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil =>
    exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel]⟩
  | cons first rest =>
    cases rest with
    | nil =>
      exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel]⟩
    | cons second rest =>
      cases rest with
      | nil =>
        rename_i left nextLeft right nextRight
        have firstDecoded := valueToList_related left nextLeft first
        have secondDecoded := valueToList_related right nextRight second
        cases firstRun : valueToList left with
        | none =>
          cases nextFirstRun : valueToList nextLeft with
          | none =>
            exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock, nextFirstRun], by
              simp [doApp, applyBlock, firstRun, AppResultRel, ResultRel]⟩
          | some xs => simp [firstRun, nextFirstRun, optionRel] at firstDecoded
        | some xs =>
          cases nextFirstRun : valueToList nextLeft with
          | none => simp [firstRun, nextFirstRun, optionRel] at firstDecoded
          | some nextXs =>
            have firstRel : List.Forall₂ ValueRel xs nextXs := by
              simpa [firstRun, nextFirstRun, optionRel] using firstDecoded
            cases secondRun : valueToList right with
            | none =>
              cases nextSecondRun : valueToList nextRight with
              | none =>
                exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock, nextFirstRun, nextSecondRun], by
                  simp [doApp, applyBlock, firstRun, secondRun, AppResultRel, ResultRel]⟩
              | some ys => simp [secondRun, nextSecondRun, optionRel] at secondDecoded
            | some ys =>
              cases nextSecondRun : valueToList nextRight with
              | none => simp [secondRun, nextSecondRun, optionRel] at secondDecoded
              | some nextYs =>
                have secondRel : List.Forall₂ ValueRel ys nextYs := by
                  simpa [secondRun, nextSecondRun, optionRel] using secondDecoded
                have appended : List.Forall₂ ValueRel (xs ++ ys) (nextXs ++ nextYs) :=
                  List.rel_append firstRel secondRel
                refine ⟨.val (listToValue (nextXs ++ nextYs), target), ?_, ?_⟩
                · simp [doApp, applyBlock, nextFirstRun, nextSecondRun]
                · simpa [doApp, applyBlock, firstRun, secondRun, AppResultRel] using
                    And.intro (listToValue_related _ _ appended) states
      | cons third rest =>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel]⟩

end Flapjack.Compiler.Backend.ClosAnnotate
