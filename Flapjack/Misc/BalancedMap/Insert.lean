import Flapjack.Misc.BalancedMap.Rotations

namespace Flapjack.Misc.BalancedMap

/-- Literal HOL insertion: comparison equality replaces the stored key as well
as its value and retains the cached size and both subtrees. The comparator is
arbitrary; no search-order or balance invariant restricts the definition. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "insert_def"]
def insert {κ ν : Type} (cmp : κ → κ → Ordering) (key : κ) (value : ν) :
    Map κ ν → Map κ ν
  | .tip => singleton key value
  | .bin n key' value' left right =>
    match cmp key key' with
    | .lt => balanceL key' value' (insert cmp key value left) right
    | .gt => balanceR key' value' left (insert cmp key value right)
    | .eq => .bin n key value left right

end Flapjack.Misc.BalancedMap
