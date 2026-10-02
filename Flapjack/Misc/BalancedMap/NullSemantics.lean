import Flapjack.Misc.BalancedMap.Semantics

namespace Flapjack.Misc.BalancedMap

/-- Full original empty-map characterization, without comparator laws or
tree invariants. Only the reviewed semantic-map representation is qualified. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "null_thm"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem nullThm {κ ι ν : Type} (cmp : κ → ι → Ordering) (tree : Map κ ν) :
    null tree = true ↔ Flapjack.Misc.BalancedMap.toFmap cmp tree =
      HolFiniteMapExact.empty := by
  classical
  cases tree with
  | tip => simp [null, toFmap]
  | bin n key value left right =>
    simp only [null, Bool.false_eq_true, false_iff]
    intro h
    have observed := congrArg (fun map => map.lookup (keySet cmp key)) h
    simp [toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at observed

end Flapjack.Misc.BalancedMap
