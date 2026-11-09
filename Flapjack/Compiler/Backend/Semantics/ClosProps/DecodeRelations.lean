module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.Equality
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Install

@[expose] public section

/-! Byte and word decoding under simple closure-value relations. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

/-- A word on the source side can relate only to the same word. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_Word64_left"]
theorem simpleValRel_word64_left (vr : Value → Value → Prop) (simple : simpleValRel vr)
    (x : Value) (word : BitVec 64) : vr (.word64 word) x ↔ x = .word64 word := by
  constructor
  · intro related
    have view := simpleValRel_view vr simple (.word64 word) x related
    cases view
    rfl
  · intro equal
    subst x
    exact (simple.2.2.1 _ word).mpr rfl

private theorem simpleValRel_number_left (vr : Value → Value → Prop) (simple : simpleValRel vr)
    (x : Value) (number : Int) : vr (.number number) x ↔ x = .number number := by
  constructor
  · intro related
    have view := simpleValRel_view vr simple (.number number) x related
    cases view
    rfl
  · intro equal
    subst x
    exact (simple.1 _ number).mpr rfl

private theorem related_mapped_left {A : Type} (vr : Value → Value → Prop) (encode : A → Value)
    (atom : ∀ a value, vr (encode a) value ↔ value = encode a)
    (items : List A) (values : List Value) :
    List.Forall₂ vr (items.map encode) values ↔ values = items.map encode := by
  induction items generalizing values with
  | nil => cases values <;> simp
  | cons item items ih =>
    cases values with
    | nil => simp
    | cons value values => simp [List.forall₂_cons, atom, ih]

private theorem related_mapped_right {A : Type} (vr : Value → Value → Prop) (encode : A → Value)
    (atom : ∀ a value, vr value (encode a) ↔ value = encode a)
    (items : List A) (values : List Value) :
    List.Forall₂ vr values (items.map encode) ↔ values = items.map encode := by
  induction items generalizing values with
  | nil => cases values <;> simp
  | cons item items ih =>
    cases values with
    | nil => simp
    | cons value values => simp [List.forall₂_cons, atom, ih]

/-- Related values produce the same byte decoder result, including failure. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_v_to_bytes"]
theorem simpleValRel_valueToBytes (vr : Value → Value → Prop) (x y : Value)
    (assumptions : simpleValRel vr ∧ vr x y) : valueToBytes x = valueToBytes y := by
  obtain ⟨simple, related⟩ := assumptions
  have lists := valueToList_related vr simple x y related
  cases left : valueToList x with
  | none =>
    cases right : valueToList y with
    | none =>
      cases l : valueToBytes x <;> cases r : valueToBytes y <;>
        simp_all [valueToBytes_eq_some]
    | some ys => simp [left, right] at lists
  | some xs =>
    cases right : valueToList y with
    | none => simp [left, right] at lists
    | some ys =>
      simp only [left, right] at lists
      apply Option.ext
      intro bytes
      rw [valueToBytes_eq_some, valueToBytes_eq_some, left, right]
      simp only [Option.some.injEq]
      constructor
      · intro eq
        subst xs
        exact (related_mapped_left vr (fun b : BitVec 8 => .number b.toNat)
          (fun _ _ => simpleValRel_number_left vr simple _ _) bytes ys).mp lists
      · intro eq
        subst ys
        exact (related_mapped_right vr (fun b : BitVec 8 => .number b.toNat)
          (fun _ _ => simple.1 _ _) bytes xs).mp lists

/-- Related values produce the same 64-bit word decoder result. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_v_to_words"]
theorem simpleValRel_valueToWords (x y : Value) (vr : Value → Value → Prop)
    (assumptions : simpleValRel vr ∧ vr x y) : valueToWords x = valueToWords y := by
  obtain ⟨simple, related⟩ := assumptions
  have lists := valueToList_related vr simple x y related
  cases left : valueToList x with
  | none =>
    cases right : valueToList y with
    | none =>
      cases l : valueToWords x <;> cases r : valueToWords y <;>
        simp_all [valueToWords_eq_some]
    | some ys => simp [left, right] at lists
  | some xs =>
    cases right : valueToList y with
    | none => simp [left, right] at lists
    | some ys =>
      simp only [left, right] at lists
      apply Option.ext
      intro words
      rw [valueToWords_eq_some, valueToWords_eq_some, left, right]
      simp only [Option.some.injEq]
      constructor
      · intro eq
        subst xs
        exact (related_mapped_left vr Value.word64
          (fun _ _ => simpleValRel_word64_left vr simple _ _) words ys).mp lists
      · intro eq
        subst ys
        exact (related_mapped_right vr Value.word64 (fun _ _ => simple.2.2.1 _ _) words xs).mp lists

end Flapjack.Compiler.Backend.ClosProps
