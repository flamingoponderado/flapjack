module

public import Flapjack.HolRef
public import Mathlib.Data.Set.Image

@[expose] public section

/-! Successor images of sets of natural numbers. -/
namespace Flapjack

/-- Successor images are disjoint exactly when their original sets are. -/
@[hol "cakeml/misc/miscScript.sml" "DISJOINT_IMAGE_SUC"]
theorem disjointImageSucc (x y : Set Nat) :
    Disjoint (Set.image Nat.succ x) (Set.image Nat.succ y) ↔ Disjoint x y :=
  Set.disjoint_image_iff Nat.succ_injective

/-- Successor preserves the original subset-of-union condition. -/
@[hol "cakeml/misc/miscScript.sml" "IMAGE_SUC_SUBSET_UNION"]
theorem imageSucc_subset_union (x y z : Set Nat) :
    Set.image Nat.succ x ⊆ Set.image Nat.succ y ∪ Set.image Nat.succ z ↔ x ⊆ y ∪ z := by
  rw [← Set.image_union]
  exact Set.image_subset_image_iff Nat.succ_injective

end Flapjack
