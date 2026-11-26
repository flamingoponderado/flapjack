module

public import Flapjack.SemanticPrimitivesHOL
public import Flapjack.SemanticPrimitivesProps.StoreRelation
public import Flapjack.HolArb

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

/-- Original `dest_Refv_def`: the payload of a reference store entry. HOL
    defines it only on `Refv`, so the other entries are unspecified (`ARB`);
    they share the opaque `holArb` value at the payload carrier. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "dest_Refv_def"
  (total_function_inhabitants := [α])]
noncomputable def destRefv {α : Type} [Nonempty α] : StoreValue α → α
  | .refv value => value
  | _ => holArb α

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

/-- A nonempty entry list concatenates the first entry's values. -/
private theorem storeValues_cons {α : Type} (entry : StoreValue α) (rest : List (StoreValue α)) :
    storeValues (entry :: rest) = storeValueValues entry ++ storeValues rest := rfl

/-- Two related lists compose their element relation. -/
private theorem forall₂_append {α β : Type} {R : α → β → Prop} {xs zs : List α}
    {ys ws : List β} (left : List.Forall₂ R xs ys) (right : List.Forall₂ R zs ws) :
    List.Forall₂ R (xs ++ zs) (ys ++ ws) := by
  induction left with
  | nil => exact right
  | cons head _ ih => exact .cons head ih

/-- Related entries hold related value lists. -/
private theorem forall₂_storeValueValues {α β : Type} {R : α → β → Prop}
    {entry : StoreValue α} {other : StoreValue β} (related : storeValueRel R entry other) :
    List.Forall₂ R (storeValueValues entry) (storeValueValues other) := by
  cases entry
  all_goals cases other
  all_goals simp_all [storeValueRel, storeValueValues]

/-- Entry predicates agree with the predicate on the held values. -/
private theorem everyStoreValue_iff_values {α : Type} (predicate : α → Prop)
    (entry : StoreValue α) :
    everyStoreValue predicate entry ↔ ∀ value ∈ storeValueValues entry, predicate value := by
  cases entry
  all_goals simp [everyStoreValue, storeValueValues]

/-- Mapping the entries maps the concatenated values. -/
private theorem storeValues_mapStoreValue {α β : Type} (f : β → α)
    (entries : List (StoreValue β)) :
    storeValues (entries.map (mapStoreValue f)) = (storeValues entries).map f := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rw [List.map_cons, storeValues_cons, storeValues_cons, ih, List.map_append]
    cases entry
    all_goals simp [storeValueValues, mapStoreValue]

/-- A predicate on all entry payloads is exactly a predicate on the concatenation. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "EVERY_sv_every_EVERY_store_vs"]
theorem everyStoreValue_storeValues {α : Type} (predicate : α → Prop)
    (entries : List (StoreValue α)) :
    (∀ entry ∈ entries, everyStoreValue predicate entry) ↔
      ∀ value ∈ storeValues entries, predicate value := by
  induction entries with
  | nil => simp [storeValues]
  | cons entry rest ih =>
    have ih' : (∀ e ∈ rest, ∀ v ∈ storeValueValues e, predicate v) ↔
        ∀ v ∈ storeValues rest, predicate v := by
      simpa only [everyStoreValue_iff_values] using ih
    simp only [storeValues_cons, List.forall_mem_cons, List.forall_mem_append,
      everyStoreValue_iff_values, ih']

/-- A predicate on mapped payloads lifts through the entry payloads. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "EVERY_sv_every_MAP_map_sv"]
theorem everyStoreValue_mapStoreValue {α β : Type} (predicate : α → Prop) (f : β → α)
    (entries : List (StoreValue β))
    (every : ∀ value ∈ (storeValues entries).map f, predicate value) :
    ∀ entry ∈ entries.map (mapStoreValue f), everyStoreValue predicate entry := by
  rw [everyStoreValue_storeValues]
  rw [storeValues_mapStoreValue]
  exact every

/-- Entry-wise predicates imply the concatenated predicate. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "EVERY_store_vs_intro"]
theorem everyStoreValue_storeValues_intro {α : Type} (predicate : α → Prop)
    (entries : List (StoreValue α))
    (every : ∀ entry ∈ entries, everyStoreValue predicate entry) :
    ∀ value ∈ storeValues entries, predicate value :=
  (everyStoreValue_storeValues predicate entries).mp every

/-- A related entry list has related concatenated payloads. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "LIST_REL_store_vs_intro"]
theorem forall₂_storeValues {α β : Type} (R : α → β → Prop)
    (left : List (StoreValue α)) (right : List (StoreValue β))
    (related : List.Forall₂ (storeValueRel R) left right) :
    List.Forall₂ R (storeValues left) (storeValues right) := by
  induction left generalizing right with
  | nil => cases related with | nil => exact .nil
  | cons entry rest ih =>
    cases related with
    | cons head tail =>
      rw [storeValues_cons, storeValues_cons]
      exact forall₂_append (forall₂_storeValueValues head) (ih _ tail)

end Flapjack.SemanticPrimitivesProps
