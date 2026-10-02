import Flapjack.Misc.BalancedMap.Domain
import Flapjack.Misc.BalancedMap.KeyOrderedSemantics
import Mathlib.Data.Set.Disjoint

namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison

/-- Full HOL invariant equation. Semantic domains are defined canonical
lookups of the reviewed producer. Comparator laws guard precisely the three
semantic consequences inside the equation; they are not outer premises. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "invariant_eq"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem invariantEq {κ β ν : Type} (cmp : κ → κ → Ordering)
    (n : Nat) (key : κ) (value : ν) (left right : Map κ ν) :
    (invariant cmp (.tip : Map κ β) ↔ True) ∧
    (invariant cmp (.bin n key value left right) ↔
      (goodCmp cmp → Disjoint
        {keys | (toFmap cmp left).lookup keys ≠ none}
        {keys | (toFmap cmp right).lookup keys ≠ none}) ∧
      (goodCmp cmp → keySet cmp key ∉
        {keys | (toFmap cmp left).lookup keys ≠ none}) ∧
      (goodCmp cmp → keySet cmp key ∉
        {keys | (toFmap cmp right).lookup keys ≠ none}) ∧
      n = 1 + structureSize left + structureSize right ∧
      keyOrdered cmp key left .gt ∧ keyOrdered cmp key right .lt ∧
      balanced (size left) (size right) ∧ invariant cmp left ∧ invariant cmp right) := by
  refine ⟨Iff.rfl, ?_⟩
  constructor
  · intro h
    rcases h with ⟨hsize, hl, hr, hbalance, hil, hir⟩
    refine ⟨?_, ?_, ?_, hsize, hl, hr, hbalance, hil, hir⟩
    · intro hgood
      apply Set.disjoint_left.mpr
      intro keys hleft hright
      obtain ⟨representative, rfl⟩ := toFmapKeySet cmp keys left hleft
      have hgt := (keySetCmpThm cmp key representative .gt hgood).mp
        ((keyOrderedToFmap cmp key left .gt hgood).mp hl _ hleft)
      have hlt := (keySetCmpThm cmp key representative .lt hgood).mp
        ((keyOrderedToFmap cmp key right .lt hgood).mp hr _ hright)
      cases hgt.symm.trans hlt
    · intro hgood hroot
      have hgt := (keySetCmpThm cmp key key .gt hgood).mp
        ((keyOrderedToFmap cmp key left .gt hgood).mp hl _ hroot)
      have heq := hgood.1 key
      cases heq.symm.trans hgt
    · intro hgood hroot
      have hlt := (keySetCmpThm cmp key key .lt hgood).mp
        ((keyOrderedToFmap cmp key right .lt hgood).mp hr _ hroot)
      have heq := hgood.1 key
      cases heq.symm.trans hlt
  · rintro ⟨_, _, _, hsize, hl, hr, hbalance, hil, hir⟩
    exact ⟨hsize, hl, hr, hbalance, hil, hir⟩

/-- Full HOL child-domain consequences, retaining the original comparator
and invariant premises and both universally quantified ordering clauses. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "inv_props"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem invProps {κ ν : Type} (cmp : κ → κ → Ordering)
    (n : Nat) (key : κ) (value : ν) (left right : Map κ ν)
    (h : goodCmp cmp ∧ invariant cmp (.bin n key value left right)) :
    Disjoint {keys | (toFmap cmp left).lookup keys ≠ none}
      {keys | (toFmap cmp right).lookup keys ≠ none} ∧
    (∀ x, (toFmap cmp left).lookup (keySet cmp x) ≠ none → cmp key x = .gt) ∧
    (∀ x, (toFmap cmp right).lookup (keySet cmp x) ≠ none → cmp key x = .lt) := by
  obtain ⟨hgood, hinv⟩ := h
  have clauses := (invariantEq (β := ν) cmp n key value left right).2.mp hinv
  refine ⟨clauses.1 hgood, ?_, ?_⟩
  · intro x hx
    exact (keySetCmpThm cmp key x .gt hgood).mp
      ((keyOrderedToFmap cmp key left .gt hgood).mp hinv.2.1 _ hx)
  · intro x hx
    exact (keySetCmpThm cmp key x .lt hgood).mp
      ((keyOrderedToFmap cmp key right .lt hgood).mp hinv.2.2.1 _ hx)

end Flapjack.Misc.BalancedMap
