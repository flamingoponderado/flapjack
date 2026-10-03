import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicCountMap
import Flapjack.Misc.Sptree.MapiWf

namespace Flapjack.WordAlloc
open RiscV

/-! Actual balanced-map branch joins correspond to the original sparse-tree
join. This implementation correspondence has no separate HOL declaration;
the reviewed original is `heuMaxAll`. Canonical well-formedness is derived
from the actual maps rather than required as an extra premise. -/

theorem heuristicCountMap_maxAll (left right : WordHeuristicCountMap) :
    heuristicCountMapToNative (left.maxAll right) =
      heuMaxAll (heuristicCountMapToNative left) (heuristicCountMapToNative right) := by
  apply (sptEqThm _ _ ⟨heuristicCountMap_wf _,
    sptWfUnion _ _ ⟨sptWfDifference _ _
      ⟨heuristicCountMap_wf left, heuristicCountMap_wf right⟩,
      sptWfMapi _ _⟩⟩).mpr
  intro key
  simp only [heuristicCountMap_lookup, WordHeuristicCountMap.lookup,
    WordHeuristicCountMap.maxAll, treeMapMergeWith_lookup,
    sptLookup_sptUnion, sptLookupDifference, sptLookupMapi]
  cases hleft : left.entries[key]? <;> cases hright : right.entries[key]? <;>
    simp [heuristicCountsToNative, wordHeuristicMax, heuMax, Nat.max_comm]

end Flapjack.WordAlloc
