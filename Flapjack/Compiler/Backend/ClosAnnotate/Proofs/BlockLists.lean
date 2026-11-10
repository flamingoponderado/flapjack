module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.StateRelation

@[expose] public section

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

end Flapjack.Compiler.Backend.ClosAnnotate
