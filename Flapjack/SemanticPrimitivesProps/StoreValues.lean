module

public import Flapjack.SemanticPrimitivesHOL

@[expose] public section

/-! Operations on the values held by source store entries. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.SemanticPrimitivesHOL

/-- Map the payload of a store entry, keeping the entry shape. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "map_sv_def"]
def mapStoreValue {α β : Type} (f : α → β) : StoreValue α → StoreValue β
  | .refv value => .refv (f value)
  | .w8array bytes => .w8array bytes
  | .varray values => .varray (values.map f)
  | .thunk mode value => .thunk mode (f value)

/-- Test whether a store entry is a reference. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "is_Refv_def"]
def isRefv {α : Type} : StoreValue α → Bool
  | .refv _ => true
  | _ => false

/-- Apply a predicate to every value directly held by a store entry. HOL's
`EVERY` fold over the array payload is rendered as membership quantification. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "sv_every_def"]
def everyStoreValue {α : Type} (predicate : α → Prop) : StoreValue α → Prop
  | .refv value => predicate value
  | .varray values => ∀ value ∈ values, predicate value
  | .thunk _ value => predicate value
  | .w8array _ => True

/-- Collect the values directly held by a store entry, in HOL's clause order. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "store_v_vs_def"]
def storeValueValues {α : Type} : StoreValue α → List α
  | .refv value => [value]
  | .varray values => values
  | .w8array _ => []
  | .thunk _ value => [value]

/-- Concatenate the values held by a list of store entries. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "store_vs_def"]
def storeValues {α : Type} (entries : List (StoreValue α)) : List α :=
  (entries.map storeValueValues).flatten

/-- Mapping twice composes the payload maps. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "map_sv_compose"]
theorem mapStoreValue_compose {α β γ : Type} (f : β → γ) (g : α → β)
    (value : StoreValue α) :
    mapStoreValue f (mapStoreValue g value) = mapStoreValue (f ∘ g) value := by
  cases value
  all_goals simp [mapStoreValue, List.map_map]

end Flapjack.SemanticPrimitivesProps
