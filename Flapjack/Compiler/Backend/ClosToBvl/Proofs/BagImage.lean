import Flapjack.Misc.Bag.Image
import Flapjack.Misc.Bag.CardOrder

/-! Bag-image monotonicity used by the closure compiler. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack

/-- Mapping a finite sub-bag preserves the sub-bag relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "BAG_IMAGE_SUB_BAG"]
theorem bagImage_subBag {α β : Type} (x y : Bag α) (f : α → β)
    (h : subBag x y ∧ finiteBag x ∧ finiteBag y) :
    subBag (bagImage f x) (bagImage f y) := by
  classical
  intro e n hn
  let P : α → Prop := fun a => f a = e
  have hx := finiteBag_filter P x h.2.1
  have hy := finiteBag_filter P y h.2.2
  have sub : subBag (bagFilter P x) (bagFilter P y) := by
    intro z k hk
    change k ≤ bagFilter P x z at hk
    change k ≤ bagFilter P y z
    by_cases hz : P z
    · have hsub : k ≤ x z := by simpa [bagFilter, hz] using hk
      have result := h.1 z k hsub
      change k ≤ y z at result
      simpa [bagFilter, hz] using result
    · simpa [bagFilter, hz] using hk
  have bound := subBag_card (bagFilter P x) (bagFilter P y) ⟨hy, sub⟩
  have hn' : n ≤ holBagCard (bagFilter P x) := by
    simpa [bagInn, bagImage, P, hx] using hn
  change n ≤ bagImage f y e
  have result := Nat.le_trans hn' bound
  simpa [bagImage, P, hy] using result

end Flapjack.Compiler.Backend.ClosToBvl
