import Flapjack.Misc.BalancedMap.InsertCorrect.Infrastructure
import Flapjack.Misc.BalancedMap.RotationCorrect.BalanceLCorrect
import Flapjack.Misc.BalancedMap.KeySets
import Flapjack.FiniteMap.MapKeys
namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison
/-- Full Less branch, with only the recursive full theorem induction result
in addition to original premises and exact branch condition. Untagged during
implementation; both original conclusions are retained. -/
theorem insertCorrectLess {κ ν : Type} (cmp : κ → κ → Ordering)
    (key root : κ) (value oldValue : ν) (n : Nat) (left right : Map κ ν)
    (hgood : goodCmp cmp) (hinv : invariant cmp (.bin n root oldValue left right))
    (hlt : cmp key root = .lt)
    (ih : invariant cmp (insert cmp key value left) ∧
      toFmap cmp (insert cmp key value left) =
        (toFmap cmp left).updateEq (keySet cmp key, value)) :
    invariant cmp (insert cmp key value (.bin n root oldValue left right)) ∧
      toFmap cmp (insert cmp key value (.bin n root oldValue left right)) =
        (toFmap cmp (.bin n root oldValue left right)).updateEq (keySet cmp key, value) := by
  classical
  rcases hinv with ⟨_, hlo, hro, hb, hil, hir⟩
  have hrootKey : cmp root key = .gt := (hgood.2.2.1 root key).mpr hlt
  have hnewOrder := keyOrderedOfSemanticUpdate cmp root key value left
    (insert cmp key value left) .gt hgood hlo hrootKey ih.2
  have halmost : almostBalancedL (size (insert cmp key value left)) (size right) := by
    rcases insertSizeGrowth cmp key value left hgood hil ih with hs | hs
    · rw [hs]; exact (almostBalancedLThm _ _ hb).1
    · rw [hs]; exact (almostBalancedLThm _ _ hb).2.1
  have hbal := balanceLThm root oldValue (insert cmp key value left) right cmp
    ⟨hgood, hnewOrder, hro, halmost, ih.1, hir⟩
  rw [insert, hlt]
  refine ⟨hbal.1, ?_⟩
  rw [hbal.2, ih.2]
  have hneq : keySet cmp key ≠ keySet cmp root := by
    intro h
    have he := (keySetEq cmp key root hgood).mp h
    cases he.symm.trans hlt
  apply HolFiniteMapExact.ext_lookup
  intro query
  simp only [toFmap, HolFiniteMapExact.lookup_updateEq, HolFiniteMapExact.lookup_union,
    FUPDATE_HOL]
  by_cases hkey : query = keySet cmp key
  · subst query
    simp [hneq]
  · by_cases hroot : query = keySet cmp root
    · simp [hroot, Ne.symm hneq]
    · simp [hkey, hroot]
end Flapjack.Misc.BalancedMap
