import Flapjack.Misc.BalancedMap.RotationAux
import Flapjack.Misc.BalancedMap.BalanceArithmetic
import Flapjack.Misc.BalancedMap.InvariantSemantics
import Flapjack.Misc.BalancedMap.StructuralSize
import Flapjack.Misc.BalancedMap.KeySets

namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison

noncomputable section
local instance {κ : Type} : DecidableEq (Set κ) := Classical.typeDecidableEq _

/-- Flapjack induction infrastructure for transitivity over the literal tree
predicate; no separate HOL declaration is claimed. -/
private theorem orderedLtTrans {κ ν : Type} (cmp : κ → κ → Ordering)
    (hgood : goodCmp cmp) (x y : κ) (tree : Map κ ν)
    (hxy : cmp x y = .lt) (hordered : keyOrdered cmp y tree .lt) :
    keyOrdered cmp x tree .lt := by
  induction tree with
  | tip => trivial
  | bin n root value left right ihl ihr =>
    exact ⟨hgood.2.2.2.2.2.2 x y root ⟨hxy, hordered.1⟩,
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

/-- Entire original single-right-rotation correctness theorem, retaining
both invariant and semantic-map preservation under all original premises. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "singleR_thm"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem singleRThm {κ ν : Type} (key : κ) (value : ν) (right : Map κ ν)
    (cmp : κ → κ → Ordering) (n : Nat) (root : κ) (rootValue : ν)
    (first middle : Map κ ν)
    (h : goodCmp cmp ∧ keyOrdered cmp key (.bin n root rootValue first middle) .gt ∧
      keyOrdered cmp key right .lt ∧ almostBalancedL n (size right) ∧
      ¬ (size right + n ≤ 1) ∧ n > delta * size right ∧
      size middle < ratio * size first ∧
      invariant cmp (.bin n root rootValue first middle) ∧ invariant cmp right) :
    invariant cmp (singleR key value (.bin n root rootValue first middle) right) ∧
    toFmap cmp (singleR key value (.bin n root rootValue first middle) right) =
      ((toFmap cmp (.bin n root rootValue first middle)).union
        (toFmap cmp right)).updateEq (keySet cmp key, value) := by
  obtain ⟨hgood, hleftOrder, hrightOrder, halmost, _hlarge, hheavy, hratio,
    hleftInv, hrightInv⟩ := h
  have hfirstSize := structureSizeThm cmp first hleftInv.2.2.2.2.1
  have hmiddleSize := structureSizeThm cmp middle hleftInv.2.2.2.2.2
  have hrightSize := structureSizeThm cmp right hrightInv
  have hn : n = size first + size middle + 1 := by
    have hs := hleftInv.1
    omega
  have hbalances := balancedLem3 (size first) (size middle) (size right)
    ⟨by simpa [hn] using halmost, by simpa [hn] using hheavy,
      hratio, hleftInv.2.2.2.1⟩
  have hrootKey : cmp root key = .lt := (hgood.2.2.1 key root).mp hleftOrder.1
  have hrootRight := orderedLtTrans cmp hgood root key right hrootKey hrightOrder
  have hinnerInv : invariant cmp (bin key value middle right) := by
    refine ⟨?_, hleftOrder.2.2, hrightOrder, hbalances.2,
      hleftInv.2.2.2.2.2, hrightInv⟩
    omega
  rw [singleRDef]
  constructor
  · have hinnerSize := structureSizeThm cmp (bin key value middle right) hinnerInv
    refine ⟨?_, hleftInv.2.1, ?_, ?_, hleftInv.2.2.2.2.1, hinnerInv⟩
    · omega
    · exact ⟨hrootKey, hleftInv.2.2.1, hrootRight⟩
    · simpa [bin, size, Nat.add_assoc] using hbalances.1
  · have hneq : keySet cmp key ≠ keySet cmp root := by
      intro heq
      have he := (keySetEq cmp key root hgood).mp heq
      cases hleftOrder.1.symm.trans he
    have hnone : (toFmap cmp first).lookup (keySet cmp key) = none := by
      by_contra hmem
      have hg := (keyOrderedToFmap cmp key first .gt hgood).mp
        hleftOrder.2.1 _ hmem
      have he := hg key (hgood.1 key)
      cases (hgood.1 key).symm.trans he
    apply mapExt
    intro keys
    by_cases hroot : keys = keySet cmp root
    · subst keys
      simp [bin, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
        HolFiniteMapExact.lookup_union, Ne.symm hneq]
    · by_cases hkey : keys = keySet cmp key
      · subst keys
        simp [bin, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_union, hneq, hnone]
      · simp only [bin, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          hroot, hkey, if_false, HolFiniteMapExact.lookup_union]
        cases (toFmap cmp first).lookup keys <;> rfl

end
end Flapjack.Misc.BalancedMap
