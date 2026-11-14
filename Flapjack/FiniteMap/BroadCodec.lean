module

public import Flapjack.FiniteMap.Exact

@[expose] public section

/-! Canonical broad view of finite-support maps for representation witnesses. -/
namespace Flapjack

/-- The broad view retains both the lookup and its finite-support evidence. -/
structure FiniteMapBroad (K V : Type) where
  lookup : K → Option V
  finiteSupport : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys

/-- Forget the exact finite-map wrapper without changing its fields. -/
def FiniteMapBroad.toBroad {K V : Type} (map : HolFiniteMapExact K V) : FiniteMapBroad K V :=
  ⟨map.lookup, map.finiteSupport⟩

/-- Reconstruct the exact finite-map wrapper from its broad view. -/
def FiniteMapBroad.ofBroad {K V : Type} (map : FiniteMapBroad K V) : HolFiniteMapExact K V :=
  ⟨map.lookup, map.finiteSupport⟩

end Flapjack
