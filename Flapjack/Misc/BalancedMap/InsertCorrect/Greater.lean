import Flapjack.Misc.BalancedMap.InsertCorrect.Infrastructure
import Flapjack.Misc.BalancedMap.RotationCorrect.BalanceRCorrect
import Flapjack.Misc.BalancedMap.KeySets
import Flapjack.FiniteMap.MapKeys
namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison
/-- Full Greater branch, with only the recursive full theorem induction result
in addition to original premises and exact branch condition. Untagged during
implementation; both original conclusions are retained. -/
theorem insertCorrectGreater {κ ν : Type} (cmp : κ → κ → Ordering)
    (key root : κ) (value oldValue : ν) (n : Nat) (left right : Map κ ν)
    (hgood : goodCmp cmp) (hinv : invariant cmp (.bin n root oldValue left right))
    (hgt : cmp key root = .gt)
    (ih : invariant cmp (insert cmp key value right) ∧
      toFmap cmp (insert cmp key value right) =
        (toFmap cmp right).updateEq (keySet cmp key, value)) :
    invariant cmp (insert cmp key value (.bin n root oldValue left right)) ∧
      toFmap cmp (insert cmp key value (.bin n root oldValue left right)) =
        (toFmap cmp (.bin n root oldValue left right)).updateEq (keySet cmp key, value) := by
  classical
  rcases hinv with ⟨_, hlo, hro, hb, hil, hir⟩
  have hrootKey : cmp root key = .lt := (hgood.2.2.1 key root).mp hgt
  have hnewOrder := keyOrderedOfSemanticUpdate cmp root key value right
    (insert cmp key value right) .lt hgood hro hrootKey ih.2
  have halmost : almostBalancedR (size left) (size (insert cmp key value right)) := by
    rcases insertSizeGrowth cmp key value right hgood hir ih with hs | hs
    · rw [hs]; exact (almostBalancedRThm _ _ hb).1
    · rw [hs]; exact (almostBalancedRThm _ _ hb).2.1
  have hbal := balanceRThm root oldValue left (insert cmp key value right) cmp
    ⟨hgood, hnewOrder, hlo, halmost, hil, ih.1⟩
  rw [insert, hgt]
  refine ⟨hbal.1, ?_⟩
  rw [hbal.2, ih.2]
  have hneq : keySet cmp key ≠ keySet cmp root := by
    intro h
    have he := (keySetEq cmp key root hgood).mp h
    cases he.symm.trans hgt
  have hleftNone : (toFmap cmp left).lookup (keySet cmp key) = none := by
    by_contra h
    have he : cmp root key = .gt := (keySetCmpThm cmp root key .gt hgood).mp
      ((keyOrderedToFmap cmp root left .gt hgood).mp hlo _ h)
    cases hrootKey.symm.trans he
  apply HolFiniteMapExact.ext_lookup
  intro query
  simp only [toFmap, HolFiniteMapExact.lookup_updateEq, HolFiniteMapExact.lookup_union,
    FUPDATE_HOL]
  by_cases hkey : query = keySet cmp key
  · subst query
    simp [hneq, hleftNone]
  · by_cases hroot : query = keySet cmp root
    · simp [hroot, Ne.symm hneq]
    · simp [hkey, hroot]
end Flapjack.Misc.BalancedMap
