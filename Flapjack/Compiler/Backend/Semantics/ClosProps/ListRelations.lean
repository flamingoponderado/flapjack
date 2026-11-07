import Flapjack.Compiler.Backend.Semantics.ClosProps.SimpleRelations

/-! Generic list-value properties of simple closure relations. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

/-- Closure-list encoding is injective. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "list_to_v_INJ"]
theorem listToValue_inj (xs ys : List Value) : listToValue xs = listToValue ys ↔ xs = ys := by
  constructor
  · intro same
    have decoded := congrArg valueToList same
    simpa [valueToList_listToValue] using decoded
  · intro same; subst ys; rfl

/-- A value related to an encoded list is itself an encoded list whose
elements are related pointwise. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "vr_list_to_v"]
theorem valueRel_listToValue (vr : Value → Value → Prop) (xs : List Value) (value : Value)
    (simple : simpleValRel vr) :
    vr value (listToValue xs) ↔ ∃ ys, value = listToValue ys ∧ List.Forall₂ vr ys xs := by
  induction xs generalizing value with
  | nil =>
    constructor
    · intro related
      obtain ⟨fields, shape, fieldsRel⟩ := (simple.2.1 value [] _).mp related
      cases fieldsRel
      exact ⟨[], by simpa [listToValue] using shape, .nil⟩
    · rintro ⟨ys, shape, rel⟩
      cases rel
      subst value
      apply (simple.2.1 _ [] _).mpr
      exact ⟨[], rfl, .nil⟩
  | cons x xs ih =>
    constructor
    · intro related
      obtain ⟨fields, shape, fieldsRel⟩ := (simple.2.1 value [x, listToValue xs] _).mp related
      cases fieldsRel with
      | cons head tail =>
        cases tail with
        | cons rest last =>
          cases last
          obtain ⟨ys, eq, rel⟩ := (ih _).mp rest
          subst value
          subst eq
          exact ⟨_ :: ys, rfl, .cons head rel⟩
    · rintro ⟨ys, shape, rel⟩
      cases rel with
      | cons head tail =>
        subst value
        apply (simple.2.1 _ [x, listToValue xs] _).mpr
        exact ⟨_, rfl, .cons head (.cons ((ih _).mpr ⟨_, rfl, tail⟩) .nil)⟩

/-- Appending related encoded lists preserves the relation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_APPEND"]
theorem simpleValRel_append (xs₁ ys₁ xs₂ ys₂ : List Value) (vr : Value → Value → Prop)
    (assumptions : simpleValRel vr ∧ vr (listToValue xs₁) (listToValue xs₂) ∧
      vr (listToValue ys₁) (listToValue ys₂)) :
    vr (listToValue (xs₁ ++ ys₁)) (listToValue (xs₂ ++ ys₂)) := by
  obtain ⟨simple, xsRel, ysRel⟩ := assumptions
  obtain ⟨xs, xsEq, xsRelated⟩ := (valueRel_listToValue vr xs₂ (listToValue xs₁) simple).mp xsRel
  obtain ⟨ys, ysEq, ysRelated⟩ := (valueRel_listToValue vr ys₂ (listToValue ys₁) simple).mp ysRel
  have : xs₁ = xs := (listToValue_inj _ _).mp xsEq
  subst xs
  have : ys₁ = ys := (listToValue_inj _ _).mp ysEq
  subst ys
  exact (valueRel_listToValue vr (xs₂ ++ ys₂) _ simple).mpr ⟨_, rfl, List.rel_append xsRelated ysRelated⟩

/-- Decoding related values either fails on both sides or returns pointwise
related lists. This is Lean-side infrastructure for the source list lemmas. -/
theorem valueToList_related (vr : Value → Value → Prop) (simple : simpleValRel vr)
    (left right : Value) (related : vr left right) :
    match valueToList left, valueToList right with
    | none, none => True
    | some xs, some ys => List.Forall₂ vr xs ys
    | _, _ => False := by
  cases right with
  | number n =>
    have eq := (simple.1 left n).mp related
    subst left; simp [valueToList]
  | word64 w =>
    have eq := (simple.2.2.1 left w).mp related
    subst left; simp [valueToList]
  | byteVector bytes =>
    have eq := (simple.2.2.2.1 left bytes).mp related
    subst left; simp [valueToList]
  | refPtr flag address =>
    have eq := (simple.2.2.2.2.1 left address flag).mp related
    subst left; simp [valueToList]
  | closure loc args env arity body =>
    have closed := simple.2.2.2.2.2.1 body arity env args loc left related
    cases left <;> simp_all [isClos, valueToList]
  | recclosure loc args env funs index =>
    have closed := simple.2.2.2.2.2.2 index funs env args loc left related
    cases left <;> simp_all [isClos, valueToList]
  | block tag fields =>
    obtain ⟨leftFields, rfl, fieldsRel⟩ := (simple.2.1 left fields tag).mp related
    cases fieldsRel with
    | nil => by_cases eq : tag = BackendCommon.nilTag <;> simp [valueToList, eq]
    | @cons first next _ _ head tail =>
      cases tail with
      | nil => simp [valueToList]
      | @cons last nextLast _ _ body rest =>
        cases rest with
        | cons extra rest => simp [valueToList]
        | nil =>
          by_cases eq : tag = BackendCommon.consTag
          · have ih := valueToList_related vr simple last nextLast body
            cases l : valueToList last <;> cases r : valueToList nextLast <;>
              simp_all [valueToList]
          · simp [valueToList, eq]
termination_by sizeOf left
decreasing_by simp_all; omega

/-- If the target is not a well-formed encoded list, neither is the related
source value. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "vr_list_NONE"]
theorem valueRel_list_none (x x₁ : Value) (vr : Value → Value → Prop)
    (assumptions : simpleValRel vr ∧ vr x x₁ ∧ valueToList x₁ = none) :
    valueToList x = none := by
  obtain ⟨simple, related, targetNone⟩ := assumptions
  have observed := valueToList_related vr simple x x₁ related
  rw [targetNone] at observed
  cases left : valueToList x <;> simp_all

/-- If a related target decodes as a list, the source decodes as a related
list and their encoded forms are related. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_list"]
theorem simpleValRel_list (x x₁ : Value) (xs : List Value) (vr : Value → Value → Prop)
    (assumptions : simpleValRel vr ∧ vr x x₁ ∧ valueToList x₁ = some xs) :
    ∃ xs₁, vr (listToValue xs₁) (listToValue xs) ∧ valueToList x = some xs₁ := by
  obtain ⟨simple, related, target⟩ := assumptions
  have observed := valueToList_related vr simple x x₁ related
  rw [target] at observed
  cases left : valueToList x with
  | none => simp [left] at observed
  | some xs₁ =>
    have fields : List.Forall₂ vr xs₁ xs := by simpa [left] using observed
    exact ⟨xs₁, (valueRel_listToValue vr xs _ simple).mpr ⟨xs₁, rfl, fields⟩, rfl⟩

end Flapjack.Compiler.Backend.ClosProps
