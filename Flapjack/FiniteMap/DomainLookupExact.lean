module

public import Flapjack.FiniteMap.DomainExact
public import Flapjack.Pancake.Semantics.PanCommonProps.FiniteMapExact

@[expose] public section

/-!
# Domain membership and lookup

Counterpart of `FDOM_FLOOKUP` from `cakeml/misc/miscScript.sml`, stated over the
reviewed canonical `HolFiniteMapExact` carrier: HOL `FDOM` is the carrier's
`domain` set and `FLOOKUP` is its `lookup`. The standalone map parameter is
recorded with `fmap_as_finite_support_parameters` and the canonical roundtrip
witness; the broad helpers come from the `pan_commonProps` exact carrier module.
-/

namespace Flapjack

/-- Canonical standalone-map witness for the exact `FDOM_FLOOKUP` parameter. -/
theorem holFmapAsFiniteSupportParamWitness_fdomFlookupHOL_f {α β : Type}
    (f : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup f) f.finiteSupport = f := by
  cases f
  rfl

/-- Original `FDOM_FLOOKUP`: domain membership is exactly a defined lookup. -/
@[hol "cakeml/misc/miscScript.sml" "FDOM_FLOOKUP"
  (fmap_as_finite_support_parameters := [f])]
theorem fdomFlookupHOL {α β : Type} (x : α) (f : HolFiniteMapExact α β) :
    x ∈ f.domain ↔ ∃ v, f.lookup x = some v := by
  show f.lookup x ≠ none ↔ ∃ v, f.lookup x = some v
  constructor
  · intro h
    cases hx : f.lookup x with
    | none => exact absurd hx h
    | some v => exact ⟨v, rfl⟩
  · rintro ⟨v, hv⟩
    rw [hv]
    simp

end Flapjack
