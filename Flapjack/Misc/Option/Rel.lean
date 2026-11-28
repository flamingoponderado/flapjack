module

public import Flapjack.HolRef

@[expose] public section

/-! The option relation from the pinned HOL option theory. -/
namespace Flapjack

/-- The HOL option relation, presented by its four constructor cases. -/
@[hol "hol4/src/coretypes/optionScript.sml" "OPTREL_def"]
def optionRel {A B : Type} (relation : A → B → Prop) : Option A → Option B → Prop
  | none, none => True
  | some left, some right => relation left right
  | _, _ => False

/-- The HOL-shaped relation agrees with Lean's inductive `Option.Rel`.
This bridge is Flapjack infrastructure, not a separate HOL declaration. -/
theorem optionRel_iff_core {A B : Type} (relation : A → B → Prop)
    (left : Option A) (right : Option B) :
    optionRel relation left right ↔ Option.Rel relation left right := by
  cases left with
  | none =>
    cases right with
    | none => exact ⟨fun _ => .none, fun _ => trivial⟩
    | some _ => exact ⟨False.elim, fun h => by cases h⟩
  | some left =>
    cases right with
    | none => exact ⟨False.elim, fun h => by cases h⟩
    | some right =>
      change relation left right ↔ Option.Rel relation (some left) (some right)
      exact ⟨Option.Rel.some, fun h => by cases h with | some related => exact related⟩

/-- Original `OPTREL_trans` (`miscScript.sml`): the option relation is
transitive once the underlying relation is transitive at the observed
witnesses. HOL's single conjunction premise is kept as one hypothesis.
-/
@[hol "cakeml/misc/miscScript.sml" "OPTREL_trans"]
theorem optionRel_trans {α : Type} (R : α → α → Prop) (x y z : Option α)
    (h : (∀ a b c, x = some a ∧ y = some b ∧ z = some c ∧ R a b ∧ R b c → R a c) ∧
      optionRel R x y ∧ optionRel R y z) : optionRel R x z := by
  obtain ⟨htrans, hxy, hyz⟩ := h
  cases x with
  | none =>
    cases y with
    | none =>
      cases z with
      | none => trivial
      | some c => exact hyz.elim
    | some b => exact hxy.elim
  | some a =>
    cases y with
    | none => exact hxy.elim
    | some b =>
      cases z with
      | none => exact hyz.elim
      | some c => exact htrans a b c ⟨rfl, rfl, rfl, hxy, hyz⟩

end Flapjack
