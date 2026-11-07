import Flapjack.SemanticPrimitivesProps.StoreRelation

/-! Store preservation in the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The original three left-hand constructor characterizations of store relations. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "sv_rel_l_cases"]
theorem storeValueRel_leftCases {α β : Type} :
    (∀ (v : StoreValue β) (rv : α) (R : α → β → Prop),
      storeValueRel R (.refv rv) v ↔ ∃ v₂, v = .refv v₂ ∧ R rv v₂) ∧
    (∀ (xs : List (BitVec 8)) (v : StoreValue β) (R : α → β → Prop),
      storeValueRel R (.w8array xs) v ↔ v = .w8array xs) ∧
    (∀ (vs : List α) (v : StoreValue β) (R : α → β → Prop),
      storeValueRel R (.varray vs) v ↔ ∃ vs₂, v = .varray vs₂ ∧ List.Forall₂ R vs vs₂) := by
  constructor
  · intro v rv R; cases v <;> simp [storeValueRel]
  constructor
  · intro xs v R; cases v <;> simp [storeValueRel, eq_comm]
  · intro vs v R; cases v <;> simp [storeValueRel]

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
