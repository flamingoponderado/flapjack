import Flapjack.Misc.BalancedMap.RotationAux
import Flapjack.Misc.BalancedMap.BalanceArithmetic
import Flapjack.Misc.BalancedMap.InvariantSemantics
import Flapjack.Misc.BalancedMap.StructuralSize
import Flapjack.Misc.BalancedMap.KeySets

namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison

noncomputable section
local instance doubleLSetDecidableEq {κ : Type} : DecidableEq (Set κ) := Classical.typeDecidableEq _

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

/-- Tree-wide greater transitivity from the original comparator clauses;
Flapjack induction infrastructure with no separate HOL original. -/
private theorem orderedGtTrans {κ ν : Type} (cmp : κ → κ → Ordering)
    (hgood : goodCmp cmp) (x y : κ) (tree : Map κ ν)
    (hxy : cmp x y = .gt) (hordered : keyOrdered cmp y tree .gt) :
    keyOrdered cmp x tree .gt := by
  induction tree with
  | tip => trivial
  | bin n root value left right ihl ihr =>
    refine ⟨?_, ihl hordered.2.1, ihr hordered.2.2⟩
    exact (hgood.2.2.1 x root).mpr
      (hgood.2.2.2.2.2.2 root y x
        ⟨(hgood.2.2.1 y root).mp hordered.1, (hgood.2.2.1 x y).mp hxy⟩)

/-- A strictly ordered subtree cannot contain the query's own equivalence
class. Derived from literal order and original goodCmp, not a target premise. -/
private theorem absentGt {κ ν : Type} (cmp : κ → κ → Ordering)
    (hgood : goodCmp cmp) (key : κ) (tree : Map κ ν)
    (horder : keyOrdered cmp key tree .gt) :
    (toFmap cmp tree).lookup (keySet cmp key) = none := by
  by_contra hmem
  have hg := (keyOrderedToFmap cmp key tree .gt hgood).mp horder _ hmem
  have he := hg key (hgood.1 key)
  cases (hgood.1 key).symm.trans he

/-- Full original double-left rotation correctness. The inner constructor is
proved from original hypotheses; no unspecified output or post-state premise. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "doubleL_thm"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem doubleLThm {κ ν : Type} (key : κ) (value : ν) (left : Map κ ν)
    (cmp : κ → κ → Ordering) (n : Nat) (root : κ) (rootValue : ν)
    (middle last : Map κ ν)
    (h : goodCmp cmp ∧ keyOrdered cmp key (.bin n root rootValue middle last) .lt ∧
      keyOrdered cmp key left .gt ∧ almostBalancedR (size left) n ∧
      ¬ (n + size left ≤ 1) ∧ n > delta * size left ∧
      ¬ (size middle < ratio * size last) ∧
      invariant cmp (.bin n root rootValue middle last) ∧ invariant cmp left) :
    invariant cmp (doubleL key value left (.bin n root rootValue middle last)) ∧
    toFmap cmp (doubleL key value left (.bin n root rootValue middle last)) =
      ((toFmap cmp left).union
        (toFmap cmp (.bin n root rootValue middle last))).updateEq (keySet cmp key, value) := by
  obtain ⟨hgood, hrightOrder, hleftOrder, halmost, hlarge, hheavy, hratio,
    hrightInv, hleftInv⟩ := h
  have hlastSize := structureSizeThm cmp last hrightInv.2.2.2.2.2
  have hmiddleSize := structureSizeThm cmp middle hrightInv.2.2.2.2.1
  have hleftSize := structureSizeThm cmp left hleftInv
  cases middle with
  | tip =>
    have hn := hrightInv.1
    change ¬ (0 < ratio * size last) at hratio
    change n = 1 + 0 + structureSize last at hn
    simp only [ratio, delta] at hratio hheavy
    omega
  | bin m pivot pivotValue second third =>
    have hmidInv := hrightInv.2.2.2.2.1
    have hsecondSize := structureSizeThm cmp second hmidInv.2.2.2.2.1
    have hthirdSize := structureSizeThm cmp third hmidInv.2.2.2.2.2
    have hm : m = size second + size third + 1 := by
      have hs := hmidInv.1
      omega
    have hn : n = size second + size last + size third + 2 := by
      have hs := hrightInv.1
      simp only [structureSize] at hs
      omega
    have hbalances := balancedLem7 (0 : Nat) (size last) (size third) (size left) (size second)
      ⟨by simpa [hn] using halmost, by simpa [hn] using hheavy,
       by simpa [size, hm] using hratio,
       by simpa [size, hm] using hrightInv.2.2.2.1, hmidInv.2.2.2.1⟩
    have hpivotRoot : cmp pivot root = .lt :=
      (hgood.2.2.1 root pivot).mp hrightInv.2.1.1
    have hpivotKey : cmp pivot key = .gt :=
      (hgood.2.2.1 pivot key).mpr hrightOrder.2.1.1
    have hpivotLast := orderedLtTrans cmp hgood pivot root last
      hpivotRoot hrightInv.2.2.1
    have hpivotLeft := orderedGtTrans cmp hgood pivot key left hpivotKey hleftOrder
    have hleftNew : invariant cmp (bin key value left second) := by
      refine ⟨?_, hleftOrder, hrightOrder.2.1.2.1, hbalances.2.1,
        hleftInv, hmidInv.2.2.2.2.1⟩
      omega
    have hrightNew : invariant cmp (bin root rootValue third last) := by
      refine ⟨?_, hrightInv.2.1.2.2, hrightInv.2.2.1, hbalances.2.2,
        hmidInv.2.2.2.2.2, hrightInv.2.2.2.2.2⟩
      omega
    rw [doubleLDef]
    constructor
    · have hls := structureSizeThm cmp (bin key value left second) hleftNew
      have hrs := structureSizeThm cmp (bin root rootValue third last) hrightNew
      refine ⟨?_, ⟨hpivotKey, hpivotLeft, hmidInv.2.1⟩,
        ⟨hpivotRoot, hmidInv.2.2.1, hpivotLast⟩, ?_, hleftNew, hrightNew⟩
      · omega
      · simpa [bin, size, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbalances.1
    · have hkeyRoot : keySet cmp key ≠ keySet cmp root := by
        intro heq
        have he := (keySetEq cmp key root hgood).mp heq
        cases hrightOrder.1.symm.trans he
      have hkeyPivot : keySet cmp key ≠ keySet cmp pivot := by
        intro heq
        have he := (keySetEq cmp key pivot hgood).mp heq
        cases hrightOrder.2.1.1.symm.trans he
      have hpivotRootSet : keySet cmp pivot ≠ keySet cmp root := by
        intro heq
        have he := (keySetEq cmp pivot root hgood).mp heq
        cases hpivotRoot.symm.trans he
      have hleftPivot := absentGt cmp hgood pivot left hpivotLeft
      have hrootLeft := orderedGtTrans cmp hgood root pivot left
        hrightInv.2.1.1 hpivotLeft
      have hleftRoot := absentGt cmp hgood root left hrootLeft
      have hsecondRoot := absentGt cmp hgood root second hrightInv.2.1.2.1
      apply mapExt
      intro keys
      by_cases hpivot : keys = keySet cmp pivot
      · subst keys
        simp [bin, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_union, hpivotRootSet, Ne.symm hkeyPivot, hleftPivot]
      · by_cases hroot : keys = keySet cmp root
        · subst keys
          simp [bin, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
            HolFiniteMapExact.lookup_union, Ne.symm hpivotRootSet, Ne.symm hkeyRoot,
            hleftRoot, hsecondRoot]
        · by_cases hkey : keys = keySet cmp key
          · subst keys
            simp [bin, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
              HolFiniteMapExact.lookup_union, hkeyPivot]
          · simp only [bin, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
              hpivot, hroot, hkey, if_false, HolFiniteMapExact.lookup_union]
            cases (toFmap cmp left).lookup keys <;>
              cases (toFmap cmp second).lookup keys <;>
              cases (toFmap cmp third).lookup keys <;> rfl

end
end Flapjack.Misc.BalancedMap
