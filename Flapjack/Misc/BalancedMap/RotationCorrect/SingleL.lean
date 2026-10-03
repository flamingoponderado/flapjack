import Flapjack.Misc.BalancedMap.RotationAux
import Flapjack.Misc.BalancedMap.BalanceArithmetic
import Flapjack.Misc.BalancedMap.InvariantSemantics
import Flapjack.Misc.BalancedMap.StructuralSize
import Flapjack.Misc.BalancedMap.KeySets

namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison

noncomputable section
local instance singleLSetDecidableEq {κ : Type} : DecidableEq (Set κ) := Classical.typeDecidableEq _

/-- Flapjack induction infrastructure for transitivity over the literal tree
predicate; no separate HOL declaration is claimed. -/
private theorem orderedGtTrans {κ ν : Type} (cmp : κ → κ → Ordering)
    (hgood : goodCmp cmp) (x y : κ) (tree : Map κ ν)
    (hxy : cmp x y = .gt) (hordered : keyOrdered cmp y tree .gt) :
    keyOrdered cmp x tree .gt := by
  induction tree with
  | tip => trivial
  | bin n root value left right ihl ihr =>
    have transGt : ∀ a b c, cmp a b = .gt → cmp b c = .gt → cmp a c = .gt := by
      intro a b c hab hbc
      apply (hgood.2.2.1 a c).mpr
      exact hgood.2.2.2.2.2.2 c b a ⟨(hgood.2.2.1 b c).mp hbc, (hgood.2.2.1 a b).mp hab⟩
    exact ⟨transGt x y root hxy hordered.1,
      ihl hordered.2.1, ihr hordered.2.2⟩

/-- Lookup extensionality for the canonical carrier, using proof irrelevance
for finite support. This is representation infrastructure, not a HOL port. -/
private theorem mapExt {α β : Type} (left right : HolFiniteMapExact α β)
    (h : ∀ key, left.lookup key = right.lookup key) : left = right := by
  cases left with
  | mk l hl =>
    cases right with
    | mk r hr =>
      have heq : l = r := funext h
      cases heq
      rfl

/-- Entire original single-left rotation correctness with all original premises. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "singleL_thm"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem singleLThm {κ ν : Type} (key : κ) (value : ν) (left : Map κ ν)
    (cmp : κ → κ → Ordering) (n : Nat) (root : κ) (rootValue : ν)
    (middle last : Map κ ν)
    (h : goodCmp cmp ∧ keyOrdered cmp key (.bin n root rootValue middle last) .lt ∧
      keyOrdered cmp key left .gt ∧ almostBalancedR (size left) n ∧
      ¬ (size left + n ≤ 1) ∧ n > delta * size left ∧
      size middle < ratio * size last ∧
      invariant cmp (.bin n root rootValue middle last) ∧ invariant cmp left) :
    invariant cmp (singleL key value left (.bin n root rootValue middle last)) ∧
    toFmap cmp (singleL key value left (.bin n root rootValue middle last)) =
      ((toFmap cmp left).union
        (toFmap cmp (.bin n root rootValue middle last))).updateEq (keySet cmp key, value) := by
  obtain ⟨hgood, hrightOrder, hleftOrder, halmost, _hlarge, hheavy, hratio,
    hrightInv, hleftInv⟩ := h
  have hlastSize := structureSizeThm cmp last hrightInv.2.2.2.2.2
  have hmiddleSize := structureSizeThm cmp middle hrightInv.2.2.2.2.1
  have hleftSize := structureSizeThm cmp left hleftInv
  have hn : n = size middle + size last + 1 := by
    have hs := hrightInv.1
    omega
  have hbalances := balancedLem6 (size middle) (size last) (size left)
    ⟨by simpa [hn] using halmost, by simpa [hn] using hheavy,
      hratio, hrightInv.2.2.2.1⟩
  have hrootKey : cmp root key = .gt := (hgood.2.2.1 root key).mpr hrightOrder.1
  have hrootLeft := orderedGtTrans cmp hgood root key left hrootKey hleftOrder
  have hinnerInv : invariant cmp (bin key value left middle) := by
    refine ⟨?_, hleftOrder, hrightOrder.2.1, hbalances.2,
      hleftInv, hrightInv.2.2.2.2.1⟩
    omega
  rw [singleLDef]
  constructor
  · have hinnerSize := structureSizeThm cmp (bin key value left middle) hinnerInv
    refine ⟨?_, ?_, hrightInv.2.2.1, ?_, hinnerInv, hrightInv.2.2.2.2.2⟩
    · omega
    · exact ⟨hrootKey, hrootLeft, hrightInv.2.1⟩
    · simpa [bin, size, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbalances.1
  · have hneq : keySet cmp key ≠ keySet cmp root := by
      intro heq
      have he := (keySetEq cmp key root hgood).mp heq
      cases hrightOrder.1.symm.trans he
    have hnone : (toFmap cmp left).lookup (keySet cmp root) = none := by
      by_contra hmem
      have hg := (keyOrderedToFmap cmp root left .gt hgood).mp hrootLeft _ hmem
      have he := hg root (hgood.1 root)
      cases (hgood.1 root).symm.trans he
    apply mapExt
    intro keys
    by_cases hroot : keys = keySet cmp root
    · subst keys
      simp [bin, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
        HolFiniteMapExact.lookup_union, Ne.symm hneq, hnone]
    · by_cases hkey : keys = keySet cmp key
      · subst keys
        simp [bin, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_union, hneq]
      · simp only [bin, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          hroot, hkey, if_false, HolFiniteMapExact.lookup_union]
        cases (toFmap cmp left).lookup keys <;> cases (toFmap cmp middle).lookup keys <;> rfl

end
end Flapjack.Misc.BalancedMap
