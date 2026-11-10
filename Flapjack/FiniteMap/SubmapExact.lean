module

public import Flapjack.Pancake.Semantics.CrepSem.HOLState

@[expose] public section

/-! Submaps on the canonical HOL finite-map carrier. -/
namespace Flapjack.HolFiniteMapExact

/-- Lookup characterization of `SUBMAP_DEF` in
    `HOL/src/finite_maps/finite_mapScript.sml`: each binding of the first map
    appears unchanged in the second. This is shared infrastructure for the
    HOL finite-map library operation. -/
def submap {α β : Type} (f g : HolFiniteMapExact α β) : Prop :=
  ∀ key value, f.lookup key = some value → g.lookup key = some value

/-- Every canonical finite map is a submap of itself. -/
theorem submap_refl {α β : Type} (f : HolFiniteMapExact α β) : f.submap f := by
  intro _ _ found
  exact found

/-- Canonical finite-map submap is transitive. -/
theorem submap_trans {α β : Type} {f g h : HolFiniteMapExact α β}
    (first : f.submap g) (second : g.submap h) : f.submap h := by
  intro key value found
  exact second key value (first key value found)

end Flapjack.HolFiniteMapExact
