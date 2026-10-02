import Flapjack.Compiler.Backend.RegAlloc.ProductionPreferences

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc

/-- Prioritised move-table carrier relation at every key, including extension
keys. Untagged Flapjack actual/native infrastructure. -/
def ProductionPriorityTableRel (native : Spt (List (Nat × Nat)))
    (production : CakeNodeMap (List (Nat × Nat))) : Prop :=
  ∀ key, production.get key = sptLookup key native

private theorem insert_production (priority node partner : Nat)
    {native : Spt (List (Nat × Nat))} {production : CakeNodeMap (List (Nat × Nat))}
    (related : ProductionPriorityTableRel native production) :
    ProductionPriorityTableRel (priMoveInsert priority node partner native)
      (production.set node ((priority, partner) :: (production.get node).getD [])) := by
  intro key
  simp only [priMoveInsert, related node]
  cases lookup : sptLookup node native with
  | none =>
    by_cases equal : key = node
    · subst key
      simp [CakeNodeMap.get_set_self, sptLookup_sptInsert_same]
    · rw [CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm equal),
        sptLookup_sptInsert_ne node key _ _ equal]
      exact related key
  | some partners =>
    by_cases equal : key = node
    · subst key
      simp [CakeNodeMap.get_set_self, sptLookup_sptInsert_same]
    · rw [CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm equal),
        sptLookup_sptInsert_ne node key _ _ equal]
      exact related key

/-- Complete executed head-first, two-endpoint move insertion agrees with
native movesToSp, including identical endpoints and arbitrary outside keys.
This is correspondence infrastructure, not another HOL definition port. -/
theorem movesToSp_production (moves : List (Nat × (Nat × Nat)))
    {native : Spt (List (Nat × Nat))} {production : CakeNodeMap (List (Nat × Nat))}
    (related : ProductionPriorityTableRel native production) :
    ProductionPriorityTableRel (movesToSp moves native) (cakeMovesToSp moves production) := by
  induction moves generalizing native production with
  | nil => exact related
  | cons move rest ih =>
    obtain ⟨priority, x, y⟩ := move
    simp only [movesToSp, cakeMovesToSp, undirMoveInsert]
    exact ih (insert_production priority x y (insert_production priority y x related))

/-- Sorting and priority removal turn the complete producer relation into the
concrete callback table relation. Equal-priority order uses the same reviewed
native mergesort, without stability assumptions. Untagged infrastructure. -/
theorem resortMoves_production
    {native : Spt (List (Nat × Nat))} {production : CakeNodeMap (List (Nat × Nat))}
    (related : ProductionPriorityTableRel native production) :
    ProductionMoveTableRel (resortMoves native) (cakeResortMovesSp production) := by
  intro key
  simp only [resortMoves, cakeResortMovesSp, CakeNodeMap.get_mapValues,
    sptLookup_sptMap, related key, cakeSort_eq_literal, sortMoves]

/-- The actual empty table used by cakeDoRegAllocFromState represents native
LN at all keys. This constructs the producer premise rather than assuming
the final preference table relation. -/
theorem emptyPriorityTable_production (dimension : Nat) :
    ProductionPriorityTableRel .ln (CakeNodeMap.ofSize dimension) := by
  intro key
  have lookup := CakeNodeMap.get_ofNatInfoMap
    (α := List (Nat × Nat)) dimension [] key
  simpa [CakeNodeMap.ofNatInfoMap, cakeMapLookup, lookupNatInfo, sptLookup] using lookup

/-- Complete table production on the executed allocator path, from the empty
array table through both-endpoint insertion and priority sorting. No output
lookup or partner-domain hypothesis is needed. Untagged correspondence. -/
theorem preferenceTable_production (dimension : Nat) (moves : List (Nat × (Nat × Nat))) :
    ProductionMoveTableRel (resortMoves (movesToSp moves .ln))
      (cakeResortMovesSp (cakeMovesToSp moves (CakeNodeMap.ofSize dimension))) :=
  resortMoves_production (movesToSp_production moves (emptyPriorityTable_production dimension))

end Flapjack.RegAlloc
