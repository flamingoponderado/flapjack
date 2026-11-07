import Flapjack.SemanticPrimitivesProps.StoreRelation

/-! Store preservation in the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- A successful assignment to related stores has a related target assignment. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "store_assign"]
theorem storeAssign_simulation {α β : Type} (index : Nat) (value : StoreValue α)
    (refs refs₂ : Store α) (R : α → β → Prop) (refs₃ : Store β) (value' : StoreValue β)
    (premises : storeAssign index value refs = some refs₂ ∧
      List.Forall₂ (storeValueRel R) refs refs₃ ∧ storeValueRel R value value') :
    ∃ refs₄, List.Forall₂ (storeValueRel R) refs₂ refs₄ ∧ storeAssign index value' refs₃ = some refs₄ := by
  obtain ⟨assigned, stores, values⟩ := premises
  obtain ⟨refs₄, assigned', related⟩ := storeAssign_related stores index values assigned
  exact ⟨refs₄, related, assigned'⟩

/-- A successful lookup in related stores yields a related target entry. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "store_lookup"]
theorem storeLookup_simulation {α β : Type} (R : α → β → Prop) (refs : Store α) (refs' : Store β)
    (index : Nat) (value : StoreValue α)
    (premises : List.Forall₂ (storeValueRel R) refs refs' ∧ storeLookup index refs = some value) :
    ∃ value', storeValueRel R value value' ∧ storeLookup index refs' = some value' := by
  obtain ⟨stores, found⟩ := premises
  obtain ⟨value', found', related⟩ := storeValueRel_lookup stores index value found
  exact ⟨value', related, found'⟩

end Flapjack.Compiler.Backend.SourceEval.Proofs
