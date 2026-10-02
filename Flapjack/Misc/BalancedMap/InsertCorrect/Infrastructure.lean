import Flapjack.Misc.BalancedMap.Insert
import Flapjack.Misc.BalancedMap.CardinalityCorrect
import Flapjack.Misc.BalancedMap.AlmostBalanceCorrect
namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison
/-- Insertion-induction infrastructure without a separate HOL declaration.
The premise is precisely the recursive invariant/map-update induction result;
the final insert theorem must establish it for each subtree. -/
theorem insertSizeGrowth {κ ν : Type} (cmp : κ → κ → Ordering)
    (key : κ) (value : ν) (tree : Map κ ν) (hgood : goodCmp cmp)
    (hinv : invariant cmp tree)
    (ih : invariant cmp (insert cmp key value tree) ∧
      toFmap cmp (insert cmp key value tree) =
        (toFmap cmp tree).updateEq (keySet cmp key, value)) :
    size (insert cmp key value tree) = size tree ∨
      size (insert cmp key value tree) = size tree + 1 := by
  classical
  rw [sizeThm cmp _ hgood ih.1, ih.2, HolFiniteMapExact.card_updateEq,
    ← sizeThm cmp tree hgood hinv]
  split_ifs <;> omega

/-- Domain-order transport through the recursive semantic update. Local proof
infrastructure, not a replacement assumption for full insertion correctness. -/
theorem keyOrderedOfSemanticUpdate {κ ν : Type} (cmp : κ → κ → Ordering)
    (root key : κ) (value : ν) (tree newTree : Map κ ν) (result : Ordering)
    (hgood : goodCmp cmp) (hold : keyOrdered cmp root tree result)
    (hkey : cmp root key = result)
    (hmap : toFmap cmp newTree = (toFmap cmp tree).updateEq (keySet cmp key, value)) :
    keyOrdered cmp root newTree result := by
  classical
  apply (keyOrderedToFmap cmp root newTree result hgood).mpr
  intro keys hdefined
  rw [hmap, HolFiniteMapExact.lookup_updateEq] at hdefined
  by_cases heq : keys = keySet cmp key
  · subst keys
    exact (keySetCmpThm cmp root key result hgood).mpr hkey
  · have hlookup : (toFmap cmp tree).lookup keys ≠ none := by
      simpa only [FUPDATE_HOL, heq, if_false] using hdefined
    exact (keyOrderedToFmap cmp root tree result hgood).mp hold keys hlookup
end Flapjack.Misc.BalancedMap
