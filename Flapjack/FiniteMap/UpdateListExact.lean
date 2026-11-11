module

public import Flapjack.Pancake.Semantics.CrepSem.HOLState

@[expose] public section

/-! HOL list updates in the canonical finite-support representation. -/
namespace Flapjack.HolFiniteMapExact

/-- Update a finite map from left to right using HOL logical equality. -/
@[hol "HOL/src/finite_maps/finite_mapScript.sml" "FUPDATE_LIST" (fmap_as_finite_support_result)]
noncomputable def holUpdateList {K V : Type} (map : HolFiniteMapExact K V)
    (entries : List (K × V)) : HolFiniteMapExact K V := by
  classical
  exact map.updateListEq entries

/-- Lookup agrees with the independently defined HOL-shaped update fold. -/
theorem holFmapAsFiniteSupportResultWitness_holUpdateList {K V : Type}
    (map : HolFiniteMapExact K V) (entries : List (K × V)) (key : K) :
    (holUpdateList map entries).lookup key = @FUPDATE_LIST_HOL K V (Classical.typeDecidableEq K) map.lookup entries key := by
  classical
  rfl

end Flapjack.HolFiniteMapExact
