import Flapjack.Misc.BalancedMap.Insert
import Flapjack.Misc.BalancedMap.Invariants
import Flapjack.Misc.BalancedMap.Semantics
import Flapjack.FiniteMap.MapKeys
namespace Flapjack.Misc.BalancedMap
/-- Full Tip branch of insertion correctness, untagged during implementation. -/
theorem insertCorrectTip {κ ν : Type} (cmp : κ → κ → Ordering)
    (key : κ) (value : ν) :
    invariant cmp (insert cmp key value .tip) ∧
      toFmap cmp (insert cmp key value .tip) =
        (toFmap cmp (.tip : Map κ ν)).updateEq (keySet cmp key, value) := by
  classical
  constructor
  · simp [insert, singleton, invariant, structureSize, keyOrdered, balanced, size]
  · apply HolFiniteMapExact.ext_lookup
    intro query
    simp [insert, singleton, toFmap, HolFiniteMapExact.lookup_union,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
end Flapjack.Misc.BalancedMap
