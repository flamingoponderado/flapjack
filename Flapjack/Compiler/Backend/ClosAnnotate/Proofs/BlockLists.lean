module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Primitive

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

/-- Related values decode either to two failures or to related lists. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "v_to_list"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem valueToList_relation (left right : Value) (related : ValueRel left right) :
    (valueToList left = none ∧ valueToList right = none) ∨
      ∃ xs ys, valueToList left = some xs ∧ valueToList right = some ys ∧
        List.Forall₂ ValueRel xs ys := by
  have decoded := ClosProps.valueToList_related ValueRel valueRelSimple left right related
  cases leftRun : valueToList left with
  | none =>
    cases rightRun : valueToList right <;> simp_all
  | some xs =>
    cases rightRun : valueToList right <;> simp_all

end Flapjack.Compiler.Backend.ClosAnnotate
