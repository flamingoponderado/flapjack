module

public import Flapjack.Misc.BalancedMap.Invariants
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Flapjack.Misc.BalancedMap

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "structure_size_thm"]
theorem structureSizeThm {κ ν : Type} (cmp : κ → κ → Ordering) (tree : Map κ ν)
    (h : invariant cmp tree) : size tree = structureSize tree := by
  cases tree with
  | tip => rfl
  | bin n key value left right => exact h.1

/-- Constructor constraint derived from the literal invariant. Flapjack proof
infrastructure shared by the rotation proofs, with no separate HOL declaration:
it adds no theorem premise. -/
theorem zeroSizeTip {κ ν : Type} (cmp : κ → κ → Ordering)
    (tree : Map κ ν) (hinv : invariant cmp tree) (hzero : size tree = 0) :
    tree = .tip := by
  have hs := structureSizeThm cmp tree hinv
  cases tree with
  | tip => rfl
  | bin n key value left right =>
    change n = 1 + structureSize left + structureSize right at hs
    change n = 0 at hzero
    omega

end Flapjack.Misc.BalancedMap
