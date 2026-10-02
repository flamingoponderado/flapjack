import Flapjack.Misc.BalancedMap.InvariantSemantics
import Flapjack.Misc.BalancedMap.KeySets

namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison

/-- Full HOL lookup correctness under exactly the original comparator and
tree invariant premises. Canonical lookup represents the semantic FLOOKUP. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "lookup_thm"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem lookupThm {κ ν : Type} (cmp : κ → κ → Ordering)
    (key : κ) (tree : Map κ ν) (h : goodCmp cmp ∧ invariant cmp tree) :
    lookup cmp key tree = (toFmap cmp tree).lookup (keySet cmp key) := by
  classical
  obtain ⟨hgood, hinv⟩ := h
  induction tree with
  | tip => rfl
  | bin n root value left right ihleft ihright =>
    have props := invProps cmp n root value left right ⟨hgood, hinv⟩
    have hl := ihleft hinv.2.2.2.2.1
    have hr := ihright hinv.2.2.2.2.2
    have same := keySetEq cmp key root hgood
    cases hc : cmp key root with
    | eq =>
      have hs := same.mpr hc
      simp [lookup, hc, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hs]
    | lt =>
      have hs : keySet cmp key ≠ keySet cmp root := by
        intro hs
        have := same.mp hs
        simp [hc] at this
      have absent : (toFmap cmp right).lookup (keySet cmp key) = none := by
        by_contra hright
        have hlt := props.2.2 key hright
        have hgt := (hgood.2.2.1 root key).mpr hc
        cases hlt.symm.trans hgt
      simp only [lookup, hc, toFmap, HolFiniteMapExact.lookup_updateEq,
        FUPDATE_HOL, hs, if_false, HolFiniteMapExact.lookup_union]
      rw [← hl, absent]
      cases lookup cmp key left <;> rfl
    | gt =>
      have hs : keySet cmp key ≠ keySet cmp root := by
        intro hs
        have := same.mp hs
        simp [hc] at this
      have absent : (toFmap cmp left).lookup (keySet cmp key) = none := by
        by_contra hleft
        have hgt := props.2.1 key hleft
        have hlt := (hgood.2.2.1 key root).mp hc
        cases hgt.symm.trans hlt
      simp only [lookup, hc, toFmap, HolFiniteMapExact.lookup_updateEq,
        FUPDATE_HOL, hs, if_false, HolFiniteMapExact.lookup_union, absent]
      exact hr

end Flapjack.Misc.BalancedMap
