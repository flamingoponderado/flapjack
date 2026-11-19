module

public import Flapjack.FiniteMap.Exact
public import Mathlib.Data.Set.Basic

@[expose] public section

/-!
# HOL `FDOM` on the canonical finite-map carrier

HOL's `FDOM` of a finite map is the set of keys with a defined lookup. This
module states that observation for the canonical `HolFiniteMapExact` carrier
and makes its membership decidable, so HOL's `IN FDOM` guards can be written
literally inside a `if`/`decide`.

Both declarations are Flapjack infrastructure with no separate HOL
declaration to port; the HOL original is `FDOM`.
-/
namespace Flapjack

/-- HOL `FDOM` for the canonical finite-map carrier: the keys with a defined
    value. -/
def HolFiniteMapExact.dom {α β : Type} (map : HolFiniteMapExact α β) : Set α :=
  { key | map.lookup key ≠ none }

/-- Flapjack helper: domain membership is decidable from the value type's
    `DecidableEq`, so HOL's `IN FDOM` guards can be written literally inside an
    `if`. -/
instance HolFiniteMapExact.decidableMemDom {α β : Type} [DecidableEq β]
    (map : HolFiniteMapExact α β) (key : α) : Decidable (key ∈ map.dom) :=
  decidable_of_iff (map.lookup key ≠ none) Iff.rfl

end Flapjack
