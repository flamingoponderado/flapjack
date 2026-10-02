import Flapjack.Misc.BalancedMap.Semantics

namespace Flapjack.Misc.BalancedMap

/-- Full HOL domain theorem, for arbitrary comparators and malformed cached
    sizes. HOL `ks ∈ FDOM (to_fmap cmp t)` is a defined canonical lookup.
    The named producer's reviewed result representation is the only qualified
    difference: no map binder, comparator law or invariant premise is added. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "to_fmap_key_set"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem toFmapKeySet {κ ν : Type} (cmp : κ → κ → Ordering)
    (keys : Set κ) (tree : Map κ ν)
    (h : (Flapjack.Misc.BalancedMap.toFmap cmp tree).lookup keys ≠ none) :
    ∃ key, keys = keySet cmp key := by
  classical
  induction tree with
  | tip => simp [toFmap, HolFiniteMapExact.lookup_empty] at h
  | bin n key value left right ihleft ihright =>
    by_cases hroot : keys = keySet cmp key
    · exact ⟨key, hroot⟩
    · simp only [toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
        hroot, if_false, HolFiniteMapExact.lookup_union] at h
      cases hleft : (toFmap cmp left).lookup keys with
      | none => exact ihright (by simpa [hleft] using h)
      | some value => exact ihleft (by simp [hleft])

end Flapjack.Misc.BalancedMap
