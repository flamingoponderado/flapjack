import Flapjack.Misc.BalancedMap.RotationAux
import Flapjack.Misc.BalancedMap.BalanceArithmetic
import Flapjack.Misc.BalancedMap.InvariantSemantics
import Flapjack.Misc.BalancedMap.StructuralSize
import Flapjack.Misc.BalancedMap.KeySets

namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison

noncomputable section
local instance doubleRSetDecidableEq {κ : Type} : DecidableEq (Set κ) := Classical.typeDecidableEq _

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

/-- Entire original double-right-rotation correctness theorem. The original
premises prove the inner Bin constructor exists before its specified equation
is used; no unspecified output or target invariant/map fact is assumed. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "doubleR_thm"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem doubleRThm {κ ν : Type} (key : κ) (value : ν) (right : Map κ ν)
    (cmp : κ → κ → Ordering) (n : Nat) (root : κ) (rootValue : ν)
    (first middle : Map κ ν)
    (h : goodCmp cmp ∧ keyOrdered cmp key (.bin n root rootValue first middle) .gt ∧
      keyOrdered cmp key right .lt ∧ almostBalancedL n (size right) ∧
      ¬ (size right + n ≤ 1) ∧ n > delta * size right ∧
      ¬ (size middle < ratio * size first) ∧
      invariant cmp (.bin n root rootValue first middle) ∧ invariant cmp right) :
    invariant cmp (doubleR key value (.bin n root rootValue first middle) right) ∧
    toFmap cmp (doubleR key value (.bin n root rootValue first middle) right) =
      ((toFmap cmp (.bin n root rootValue first middle)).union
        (toFmap cmp right)).updateEq (keySet cmp key, value) := by
  obtain ⟨hgood, hleftOrder, hrightOrder, halmost, hlarge, hheavy, hratio,
    hleftInv, hrightInv⟩ := h
  have hfirstSize := structureSizeThm cmp first hleftInv.2.2.2.2.1
  have hmiddleSize := structureSizeThm cmp middle hleftInv.2.2.2.2.2
  have hrightSize := structureSizeThm cmp right hrightInv
  cases middle with
  | tip =>
    have hn := hleftInv.1
    change ¬ (0 < ratio * size first) at hratio
    change n = 1 + structureSize first + 0 at hn
    simp only [ratio, delta] at hratio hheavy
    omega
  | bin m pivot pivotValue second third =>
    have hmidInv := hleftInv.2.2.2.2.2
    have hsecondSize := structureSizeThm cmp second hmidInv.2.2.2.2.1
    have hthirdSize := structureSizeThm cmp third hmidInv.2.2.2.2.2
    have hm : m = size second + size third + 1 := by
      have hs := hmidInv.1
      omega
    have hn : n = size first + size second + size third + 2 := by
      have hs := hleftInv.1
      simp only [structureSize] at hs
      omega
    have hbalances := balancedLem4 (size first) (size second) (size third) (size right)
      ⟨by simpa [hn] using halmost, by simpa [hn] using hheavy,
       by simpa [size, hm] using hratio,
       by simpa [size, hm] using hleftInv.2.2.2.1, hmidInv.2.2.2.1⟩
    have hpivotRoot : cmp pivot root = .gt :=
      (hgood.2.2.1 pivot root).mpr hleftInv.2.2.1.1
    have hpivotKey : cmp pivot key = .lt :=
      (hgood.2.2.1 key pivot).mp hleftOrder.2.2.1
    have hpivotFirst := orderedGtTrans cmp hgood pivot root first
      hpivotRoot hleftInv.2.1
    have hpivotRight := orderedLtTrans cmp hgood pivot key right hpivotKey hrightOrder
    have hleftNew : invariant cmp (bin root rootValue first second) := by
      refine ⟨?_, hleftInv.2.1, hleftInv.2.2.1.2.1, hbalances.2.1,
        hleftInv.2.2.2.2.1, hmidInv.2.2.2.2.1⟩
      omega
    have hrightNew : invariant cmp (bin key value third right) := by
      refine ⟨?_, hleftOrder.2.2.2.2, hrightOrder, hbalances.2.2,
        hmidInv.2.2.2.2.2, hrightInv⟩
      omega
    rw [doubleRDef]
    constructor
    · have hls := structureSizeThm cmp (bin root rootValue first second) hleftNew
      have hrs := structureSizeThm cmp (bin key value third right) hrightNew
      refine ⟨?_, ⟨hpivotRoot, hpivotFirst, hmidInv.2.1⟩,
        ⟨hpivotKey, hmidInv.2.2.1, hpivotRight⟩, ?_, hleftNew, hrightNew⟩
      · omega
      · simpa [bin, size, Nat.add_assoc] using hbalances.1
    · have hkeyRoot : keySet cmp key ≠ keySet cmp root := by
        intro heq
        have he := (keySetEq cmp key root hgood).mp heq
        cases hleftOrder.1.symm.trans he
      have hkeyPivot : keySet cmp key ≠ keySet cmp pivot := by
        intro heq
        have he := (keySetEq cmp key pivot hgood).mp heq
        cases hleftOrder.2.2.1.symm.trans he
      have hpivotRootSet : keySet cmp pivot ≠ keySet cmp root := by
        intro heq
        have he := (keySetEq cmp pivot root hgood).mp heq
        cases hpivotRoot.symm.trans he
      have hfirstKey := absentGt cmp hgood key first hleftOrder.2.1
      have hsecondKey := absentGt cmp hgood key second hleftOrder.2.2.2.1
      have hfirstPivot := absentGt cmp hgood pivot first hpivotFirst
      apply mapExt
      intro keys
      by_cases hpivot : keys = keySet cmp pivot
      · subst keys
        simp [bin, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          HolFiniteMapExact.lookup_union, hpivotRootSet, Ne.symm hkeyPivot, hfirstPivot]
      · by_cases hroot : keys = keySet cmp root
        · subst keys
          simp [bin, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
            HolFiniteMapExact.lookup_union, Ne.symm hpivotRootSet, Ne.symm hkeyRoot]
        · by_cases hkey : keys = keySet cmp key
          · subst keys
            simp [bin, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
              HolFiniteMapExact.lookup_union, hkeyPivot, hkeyRoot, hfirstKey, hsecondKey]
          · simp only [bin, toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
              hpivot, hroot, hkey, if_false, HolFiniteMapExact.lookup_union]
            cases (toFmap cmp first).lookup keys <;>
              cases (toFmap cmp second).lookup keys <;> rfl

end
end Flapjack.Misc.BalancedMap
