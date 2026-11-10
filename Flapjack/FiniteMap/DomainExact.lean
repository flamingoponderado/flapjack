module

public import Flapjack.Pancake.Semantics.CrepSem.HOLState
public import Mathlib.Data.Set.Defs

@[expose] public section

namespace Flapjack.HolFiniteMapExact

/-- Defined lookup domain of the canonical carrier. Flapjack infrastructure;
HOL uses FDOM on its abstract finite-map carrier. -/
def domain (map : HolFiniteMapExact α β) : Set α := {key | map.lookup key ≠ none}

end Flapjack.HolFiniteMapExact
