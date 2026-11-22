module

public import Flapjack.FiniteMap.AlistExact
public import Flapjack.PanToCrepMaxList
public import Flapjack.Pancake.Semantics.PanCommonProps.FiniteMapExact
public import Flapjack.Pancake.Semantics.PanProps.WithShape

@[expose] public section

/-!
# HOL `all_distinct_alist_no_overlap` and `all_distinct_alist_ctxt_max`

Exact ports of the two `panPropsScript.sml` theorems that combine the
`with_shape` lemmas with the finite-map context predicates of
`pan_commonPropsScript.sml` (`:476-516` and `:517-538`).  HOL's
`alist_to_fmap (ZIP (vs, ZIP (sh, with_shape sh ns)))` is the canonical
`HolFiniteMapExact.alistToFmap` over the same nested pairs, `no_overlap` and
`ctxt_max` are the tagged `noOverlapHOL`/`ctxtMaxHOL`, `MAX_LIST` is the
executable `maxList`, `size_of_shape (Comb sh)` is `sizeOfShapeHOL (.comb sh)`
and `with_shape` is the tagged `withShapeHOL`.  The computed map is a
standalone producer result, so both declarations carry the
`fmap_as_finite_support_result_observations` qualifier for the imported tagged
producer `HolFiniteMapExact.alistToFmap`; the value type `α` is HOL's own
independent type variable and needs no word or finite-map qualifier.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (ShapeHOL sizeOfShapeHOL withShapeHOL)

/-- Exact port of HOL `panProps$all_distinct_alist_no_overlap`
    (`cakeml/pancake/semantics/panPropsScript.sml:476-516`):
    `ALL_DISTINCT ns /\ LENGTH ns = size_of_shape (Comb sh) /\
     LENGTH vs = LENGTH sh ==>
     no_overlap (alist_to_fmap (ZIP (vs, ZIP (sh, with_shape sh ns))))`.
    HOL's three conjuncts are one premise, and the binders `ns`, `sh`, `vs`
    keep HOL's free-variable order.  The first `no_overlap` conjunct reads the
    `ALL_DISTINCT` component through the tagged `allDistinctWithShapeHOL`; the
    second reads the disjointness through the tagged
    `allDistinctMemZipDisjointWithShapeHOL`.  Membership of a looked-up
    association is HOL's `ALOOKUP_MEM` step, rendered by the untagged
    `HolFiniteMapExact.lookup_alistToFmap_mem`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "all_distinct_alist_no_overlap"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.alistToFmap])]
theorem allDistinctAlistNoOverlapHOL {α : Type} :
    ∀ (ns : List Nat) (sh : List ShapeHOL) (vs : List α),
      ns.Nodup ∧ ns.length = sizeOfShapeHOL (.comb sh) ∧ vs.length = sh.length →
      noOverlapHOL
        (Flapjack.HolFiniteMapExact.alistToFmap
          (vs.zip (sh.zip (withShapeHOL sh ns)))) := by
  intro ns sh vs h
  obtain ⟨hnd, hsize, hlen⟩ := h
  refine ⟨?_, ?_⟩
  · intro x a xs hlook
    have hentry : (x, (a, xs)) ∈ vs.zip (sh.zip (withShapeHOL sh ns)) :=
      HolFiniteMapExact.lookup_alistToFmap_mem _ x (a, xs) hlook
    obtain ⟨_, hrest⟩ := List.of_mem_zip hentry
    obtain ⟨_, hxs⟩ := List.of_mem_zip hrest
    obtain ⟨n, hn, hxsEq⟩ := List.mem_iff_getElem.mp hxs
    have hn' : n < sh.length := by
      rw [withShapeHOLLength] at hn
      exact hn
    have hdistinct := allDistinctWithShapeHOL sh ns n ⟨hnd, hn', hsize⟩
    rw [← hxsEq]
    exact hdistinct
  · intro x y a b xs ys h
    obtain ⟨hlookx, hlooky, hdisj⟩ := h
    by_cases hxy : x = y
    · exact hxy
    · exfalso
      have hleftEntry : (x, (a, xs)) ∈ vs.zip (sh.zip (withShapeHOL sh ns)) :=
        HolFiniteMapExact.lookup_alistToFmap_mem _ x (a, xs) hlookx
      have hrightEntry : (y, (b, ys)) ∈ vs.zip (sh.zip (withShapeHOL sh ns)) :=
        HolFiniteMapExact.lookup_alistToFmap_mem _ y (b, ys) hlooky
      have hdisjoint := allDistinctMemZipDisjointWithShapeHOL vs sh ns x a xs y b ys
        ⟨hlen, by rw [withShapeHOLLength], hnd, hsize, hleftEntry, hrightEntry, hxy⟩
      exact hdisj hdisjoint

/-- Exact port of HOL `panProps$all_distinct_alist_ctxt_max`
    (`cakeml/pancake/semantics/panPropsScript.sml:517-538`):
    `ALL_DISTINCT ns /\ LENGTH ns = size_of_shape (Comb sh) /\
     LENGTH vs = LENGTH sh ==>
     ctxt_max (MAX_LIST ns) (alist_to_fmap (ZIP (vs, ZIP (sh, with_shape sh ns))))`.
    Same binders, premise and carriers as `all_distinct_alist_no_overlap`;
    `MAX_LIST` is `maxList` and the bound is read through the tagged
    `elMemWithShapeHOL` and `maxList_ge_of_mem`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "all_distinct_alist_ctxt_max"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.alistToFmap])]
theorem allDistinctAlistCtxtMaxHOL {α : Type} :
    ∀ (ns : List Nat) (sh : List ShapeHOL) (vs : List α),
      ns.Nodup ∧ ns.length = sizeOfShapeHOL (.comb sh) ∧ vs.length = sh.length →
      ctxtMaxHOL (maxList ns)
        (Flapjack.HolFiniteMapExact.alistToFmap
          (vs.zip (sh.zip (withShapeHOL sh ns)))) := by
  intro ns sh vs h
  obtain ⟨hnd, hsize, _hlen⟩ := h
  refine ⟨Nat.zero_le _, ?_⟩
  intro v a xs hlook x hx
  have hentry : (v, (a, xs)) ∈ vs.zip (sh.zip (withShapeHOL sh ns)) :=
    HolFiniteMapExact.lookup_alistToFmap_mem _ v (a, xs) hlook
  obtain ⟨_, hrest⟩ := List.of_mem_zip hentry
  obtain ⟨_, hxs⟩ := List.of_mem_zip hrest
  obtain ⟨n, hn, hxsEq⟩ := List.mem_iff_getElem.mp hxs
  have hmem : x ∈ elHOL (withShapeHOL sh ns) n := by
    rw [elHOL_eq_getElem _ _ hn, hxsEq]
    exact hx
  exact maxList_ge_of_mem ns x (elMemWithShapeHOL sh ns n x ⟨hn, hsize, hmem⟩)

end Flapjack
