module

public import Flapjack.FiniteMap.UnionExact
public import Flapjack.FiniteMap.Exact
public import Flapjack.Pancake.Semantics.PanCommonProps.FiniteMapExact
public import Flapjack.Pancake.Semantics.CrepSem.HOLState

@[expose] public section

/-!
# `FUNION_FUPDATE_2` over the canonical finite-support carrier

Counterpart of `FUNION_FUPDATE_2` from `HOL/src/finite_maps/finite_mapScript.sml`.
HOL's left-biased union (`FUNION`, the carrier's `union`) of `f` with an updated
`g` ignores that update whenever the key is already defined in `f`, and applies
it otherwise. `|+` is `updateEq` (HOL equality via `DecidableEq`) and `FDOM` is
the carrier's `domain`.
-/

namespace Flapjack.HolFiniteMapExact

/-- Canonical standalone-map witness for the first `FUNION_FUPDATE_2` parameter. -/
theorem holFmapAsFiniteSupportParamWitness_funionFupdate2_f {α β : Type}
    (f : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup f) f.finiteSupport = f := by
  cases f
  rfl

/-- Canonical standalone-map witness for the second `FUNION_FUPDATE_2` parameter. -/
theorem holFmapAsFiniteSupportParamWitness_funionFupdate2_g {α β : Type}
    (g : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup g) g.finiteSupport = g := by
  cases g
  rfl

open Classical in
/-- Original `FUNION_FUPDATE_2`. -/
@[hol "HOL/src/finite_maps/finite_mapScript.sml" "FUNION_FUPDATE_2"
  (fmap_as_finite_support_parameters := [f, g])]
theorem funionFupdate2 {α β : Type} [DecidableEq α] (f : HolFiniteMapExact α β)
    (g : HolFiniteMapExact α β) (x : α) (y : β) :
    f.union (g.updateEq (x, y)) =
      if x ∈ f.domain then f.union g else (f.union g).updateEq (x, y) := by
  by_cases hx : x ∈ f.domain
  · rw [if_pos hx]
    have hpoint : ∀ k, (f.union (g.updateEq (x, y))).lookup k = (f.union g).lookup k := by
      intro k
      by_cases hk : k = x
      · rw [hk]
        have hfx : f.lookup x ≠ none := hx
        simp only [lookup_union, lookup_updateEq, FUPDATE_HOL]
        cases hfl : f.lookup x
        · exact absurd hfl hfx
        · simp
      · simp [lookup_union, lookup_updateEq, FUPDATE_HOL, hk]
    cases h1 : f.union (g.updateEq (x, y)) with
    | mk l1 s1 =>
      cases h2 : f.union g with
      | mk l2 s2 =>
        simp only [h1, h2] at hpoint
        rw [HolFiniteMapExact.mk.injEq]
        exact funext hpoint
  · rw [if_neg hx]
    have hfx : f.lookup x = none := by
      cases hfl : f.lookup x with
      | none => rfl
      | some v =>
        have hne : f.lookup x ≠ none := by
          rw [hfl]
          simp
        exact absurd hne hx
    have hpoint : ∀ k, (f.union (g.updateEq (x, y))).lookup k =
        ((f.union g).updateEq (x, y)).lookup k := by
      intro k
      by_cases hk : k = x
      · rw [hk]
        simp [lookup_union, lookup_updateEq, FUPDATE_HOL, hfx]
      · simp [lookup_union, lookup_updateEq, FUPDATE_HOL, hk]
    cases h1 : f.union (g.updateEq (x, y)) with
    | mk l1 s1 =>
      cases h2 : (f.union g).updateEq (x, y) with
      | mk l2 s2 =>
        simp only [h1, h2] at hpoint
        rw [HolFiniteMapExact.mk.injEq]
        exact funext hpoint

end Flapjack.HolFiniteMapExact
