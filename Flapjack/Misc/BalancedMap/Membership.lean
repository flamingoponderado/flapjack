import Flapjack.Misc.BalancedMap.Core

namespace Flapjack.Misc.BalancedMap

/-- Full recursive membership/optional-lookup law, retaining independent query,
stored-key and payload types. No comparator law or tree invariant is assumed. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "member_eq_lookup"]
theorem memberEqLookup {ι κ ν : Type} (cmp : ι → κ → Ordering) (query : ι)
    (tree : Map κ ν) : member cmp query tree = (lookup cmp query tree).isSome := by
  induction tree with
  | tip => rfl
  | bin size key value left right ihLeft ihRight =>
    cases h : cmp query key <;> simp [member, lookup, h, ihLeft, ihRight]

end Flapjack.Misc.BalancedMap
