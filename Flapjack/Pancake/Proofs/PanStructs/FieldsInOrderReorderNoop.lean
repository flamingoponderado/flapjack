import Flapjack.Pancake.Proofs.PanStructs.CompileExpNField
namespace Flapjack.Pancake.Proofs.PanStructs.FieldsInOrderReorderNoop
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact

/-- Flapjack generic first-match field selection infrastructure. -/
def selectFields {β γ : Type}
    (ordered : List (MlS × γ)) (fields : List (MlS × β)) : List β :=
  ordered.flatMap fun entry =>
    match fields.findSome? (fun candidate =>
        if candidate.1 = entry.1 then some candidate.2 else none) with
    | none => []
    | some value => [value]

/-- Flapjack selection codec law: an absent prefix key cannot shadow any
selected field; the original theorem supplies this from distinctness. -/
theorem selectFields_skip {β γ : Type}
    (ordered : List (MlS × γ)) (fields : List (MlS × β)) (name : MlS) (value : β)
    (h : name ∉ ordered.map Prod.fst) :
    selectFields ordered ((name, value) :: fields) = selectFields ordered fields := by
  induction ordered with
  | nil => rfl
  | cons entry rest ih =>
    have hn : name ≠ entry.1 := by
      intro heq
      apply h
      simp [heq]
    have ht : name ∉ rest.map Prod.fst := by
      intro hm
      apply h
      simp [hm]
    have hs := ih ht
    simp only [selectFields, List.flatMap_cons] at hs ⊢
    simp only [List.findSome?_cons, hn, ↓reduceIte]
    simp only [List.findSome?_cons] at hs
    rw [hs]
/-- Full faithful field-order theorem. The ignored info-field payload remains
polymorphic; exact context, field names and expressions use the HOL carriers. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "fields_in_order_reorder_noop"
  (words_as_type_indexed_bitvec)]
theorem fieldsInOrderReorderNoopExact {width : Nat} [NeZero width] {α : Type}
    (context : ContextExact) (fields : List (MlS × ExpHOL width))
    (infoFields : List (MlS × α))
    (hNames : infoFields.map Prod.fst = fields.map Prod.fst)
    (hNodup : (infoFields.map Prod.fst).Nodup) :
    (infoFields.flatMap fun entry =>
      match (compileFieldsExact context fields).findSome?
          (fun candidate => if candidate.1 = entry.1 then some candidate.2 else none) with
      | none => []
      | some expression => [expression]) =
    fields.map (fun entry => compileExpExact context entry.2) := by
  have bridge : (infoFields.flatMap fun entry =>
      match (compileFieldsExact context fields).findSome?
          (fun candidate => if candidate.1 = entry.1 then some candidate.2 else none) with
      | none => []
      | some expression => [expression]) =
      selectFields infoFields (compileFieldsExact context fields) := by
    unfold selectFields
    apply congrArg (fun f => infoFields.flatMap f)
    funext entry
    cases (compileFieldsExact context fields).findSome?
      (fun candidate => if candidate.1 = entry.1 then some candidate.2 else none) <;> rfl
  rw [bridge]
  clear bridge
  induction fields generalizing infoFields with
  | nil =>
    have hn : infoFields = [] := List.map_eq_nil_iff.mp hNames
    subst infoFields
    rfl
  | cons entry rest ih =>
    obtain ⟨name, expression⟩ := entry
    cases infoFields with
    | nil => simp at hNames
    | cons infoEntry infoRest =>
      obtain ⟨infoName, payload⟩ := infoEntry
      simp only [List.map_cons, List.cons.injEq] at hNames
      obtain ⟨heq, htail⟩ := hNames
      subst infoName
      have hn : name ∉ infoRest.map Prod.fst ∧ (infoRest.map Prod.fst).Nodup := by
        simpa only [List.map_cons, List.nodup_cons] using hNodup
      have hs := selectFields_skip infoRest (compileFieldsExact context rest)
        name (compileExpExact context expression) hn.1
      have ht := ih infoRest htail hn.2
      simp only [compileFieldsExact, selectFields, List.flatMap_cons,
        List.findSome?_cons, ↓reduceIte, List.singleton_append, List.map_cons]
      change compileExpExact context expression ::
        selectFields infoRest ((name, compileExpExact context expression) ::
          compileFieldsExact context rest) = _
      rw [hs, ht]
end Flapjack.Pancake.Proofs.PanStructs.FieldsInOrderReorderNoop
