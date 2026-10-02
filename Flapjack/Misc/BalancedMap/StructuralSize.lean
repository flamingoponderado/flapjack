import Flapjack.Misc.BalancedMap.Invariants

namespace Flapjack.Misc.BalancedMap

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "structure_size_thm"]
theorem structureSizeThm {κ ν : Type} (cmp : κ → κ → Ordering) (tree : Map κ ν)
    (h : invariant cmp tree) : size tree = structureSize tree := by
  cases tree with
  | tip => rfl
  | bin n key value left right => exact h.1

end Flapjack.Misc.BalancedMap
