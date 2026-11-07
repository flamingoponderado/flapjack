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

end Flapjack
