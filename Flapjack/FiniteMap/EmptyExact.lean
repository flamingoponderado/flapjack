module

public import Flapjack.Pancake.Semantics.CrepSem.HOLState

@[expose] public section

/-! The empty HOL finite map in the canonical finite-support carrier. -/
namespace Flapjack.HolFiniteMapExact

/-- The polymorphic empty map has no bindings. -/
@[hol "HOL/src/finite_maps/finite_mapScript.sml" "FEMPTY_DEF" (fmap_as_finite_support_result)]
def holEmpty {α β : Type} : HolFiniteMapExact α β := HolFiniteMapExact.empty

/-- Every lookup in the canonical map agrees with the independent raw
empty-map codec. -/
theorem holFmapAsFiniteSupportResultWitness_holEmpty {α β : Type} (key : α) :
    (holEmpty : HolFiniteMapExact α β).lookup key = (FEMPTY : FiniteMap α β) key := rfl

end Flapjack.HolFiniteMapExact
