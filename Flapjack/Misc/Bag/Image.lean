module

public import Flapjack.Misc.Bag.Filter
public import Flapjack.Misc.Bag.Card

@[expose] public section

/-! HOL bag image, including its infinite-fiber behavior. -/
namespace Flapjack

/-- Multiplicity is the cardinality of the filtered fiber, or one if it is infinite. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_IMAGE_DEF"]
noncomputable def bagImage {α β : Type} (f : α → β) (b : Bag α) : Bag β := by
  classical
  exact fun e =>
    let filtered := bagFilter (fun e₀ => f e₀ = e) b
    if finiteBag filtered then holBagCard filtered else 1

end Flapjack
