import Flapjack.Misc.BalancedMap.Invariants
import Flapjack.Misc.BalancedMap.KeySetComparison

namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison

/-- Full HOL ordering/domain equivalence. Defined canonical lookup translates
FDOM membership; no invariant or cached-size premise is required. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "key_ordered_to_fmap"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem keyOrderedToFmap {κ ν : Type} (cmp : κ → κ → Ordering)
    (key : κ) (tree : Map κ ν) (result : Ordering) (hcmp : goodCmp cmp) :
    keyOrdered cmp key tree result ↔
      ∀ keys, (Flapjack.Misc.BalancedMap.toFmap cmp tree).lookup keys ≠ none →
        keySetCmp cmp key keys result := by
  classical
  induction tree with
  | tip => simp [keyOrdered, toFmap, HolFiniteMapExact.lookup_empty]
  | bin n root value left right ihleft ihright =>
    have domain (keys : Set κ) :
        (toFmap cmp (.bin n root value left right)).lookup keys ≠ none ↔
          keys = keySet cmp root ∨ (toFmap cmp left).lookup keys ≠ none ∨
            (toFmap cmp right).lookup keys ≠ none := by
      by_cases heq : keys = keySet cmp root
      · simp [toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, heq]
      · simp only [toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          heq, if_false, false_or]
        exact HolFiniteMapExact.union_defined_iff _ _ _
    constructor
    · rintro ⟨hroot, hleft, hright⟩ keys hkeys
      rcases (domain keys).mp hkeys with hsame | hleftKey | hrightKey
      · subst keys
        exact (keySetCmpThm cmp key root result hcmp).mpr hroot
      · exact ihleft.mp hleft keys hleftKey
      · exact ihright.mp hright keys hrightKey
    · intro hall
      refine ⟨(keySetCmpThm cmp key root result hcmp).mp
        (hall _ ((domain _).mpr (Or.inl rfl))), ?_, ?_⟩
      · exact ihleft.mpr (fun keys hkeys => hall keys
          ((domain keys).mpr (Or.inr (Or.inl hkeys))))
      · exact ihright.mpr (fun keys hkeys => hall keys
          ((domain keys).mpr (Or.inr (Or.inr hkeys))))

end Flapjack.Misc.BalancedMap
