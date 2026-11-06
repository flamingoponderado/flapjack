import Flapjack.HolRef

/-! The polymorphic HOL bag carrier and basic union laws. -/
namespace Flapjack

/-- HOL bags are functions from elements to natural multiplicities. -/
@[hol "HOL/src/bag/bagScript.sml" "bag"]
abbrev Bag (α : Type) := α → Nat

/-- The constant-zero bag. -/
@[hol "HOL/src/bag/bagScript.sml" "EMPTY_BAG"]
def emptyBag {α : Type} : Bag α := fun _ => 0

/-- Bag union adds multiplicities pointwise. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_UNION"]
def bagUnion {α : Type} (left right : Bag α) : Bag α := fun x => left x + right x

/-- The two union identities and the characterization of empty unions.
The three conjuncts have independently quantified element types, as in HOL. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_UNION_EMPTY"]
theorem bagUnion_empty {α β γ : Type} :
    (∀ b : Bag α, bagUnion b emptyBag = b) ∧
    (∀ b : Bag β, bagUnion emptyBag b = b) ∧
    (∀ b₁ b₂ : Bag γ, bagUnion b₁ b₂ = emptyBag ↔ b₁ = emptyBag ∧ b₂ = emptyBag) := by
  simp [bagUnion, emptyBag, funext_iff, Nat.add_eq_zero_iff, forall_and]

/-- Projection of the right-identity conjunct for a single bag. -/
theorem bagUnion_empty_right {α : Type} (b : Bag α) : bagUnion b emptyBag = b :=
  (bagUnion_empty (α := α) (β := α) (γ := α)).1 b

/-- Projection of the left-identity conjunct for a single bag. -/
theorem bagUnion_empty_left {α : Type} (b : Bag α) : bagUnion emptyBag b = b :=
  (bagUnion_empty (α := α) (β := α) (γ := α)).2.1 b

end Flapjack
