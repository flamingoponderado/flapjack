import Flapjack.Misc.BalancedMap.Core

namespace Flapjack.Misc.BalancedMap

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanced_def"]
def balanced (left right : Nat) : Prop :=
  left + right ≤ 1 ∨ max left right ≤ delta * min left right

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "structure_size_def"]
def structureSize {κ ν : Type} : Map κ ν → Nat
  | .tip => 0
  | .bin _ _ _ left right => 1 + structureSize left + structureSize right

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "key_ordered_def"]
def keyOrdered {ι κ ρ ν : Type} (cmp : ι → κ → ρ) (key : ι) :
    Map κ ν → ρ → Prop
  | .tip, _ => True
  | .bin _ key' _ left right, result =>
    cmp key key' = result ∧ keyOrdered cmp key left result ∧ keyOrdered cmp key right result

/-- Literal HOL invariant, retaining cached-size consistency separately from
recursive balance and key order. No comparator law is an extra premise. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "invariant_def"]
def invariant {κ ν : Type} (cmp : κ → κ → Ordering) : Map κ ν → Prop
  | .tip => True
  | .bin n key _ left right =>
    n = 1 + structureSize left + structureSize right ∧
    keyOrdered cmp key left .gt ∧ keyOrdered cmp key right .lt ∧
    balanced (size left) (size right) ∧ invariant cmp left ∧ invariant cmp right

end Flapjack.Misc.BalancedMap
