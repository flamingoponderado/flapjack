import Flapjack.Compiler.Backend.WordAlloc.ProductionCallCache
import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicCountMap

namespace Flapjack.WordAlloc
open RiscV

/-! The actual self-call cache includes precisely the tracked counter keys.
These implementation correspondences have no separate HOL original; they
connect the real cache to the reviewed original `addCall`. -/

theorem heuristicCountMap_keyProjection (counts : WordHeuristicCountMap) :
    stackNamesTree counts.keys =
      sptMap (fun _ => ()) (heuristicCountMapToNative counts) := by
  rw [WordHeuristicCountMap.keys, NumSet.fromDistinctList_eq Std.TreeMap.nodup_keys]
  change stackNamesTree (NumSet.fromList counts.entries.keys) = _
  rw [stackNamesTree, numSetFromList_production]
  exact heuristicCountMap_unitProjection counts

theorem callCache_addCall (calls : WordHeuristicCallSet) (counts : WordHeuristicCountMap)
    (valid : StackCacheRep calls.names calls.seen) :
    stackNamesTree (calls.addCall counts).names =
        addCall (heuristicCountMapToNative counts) (stackNamesTree calls.names) ∧
      StackCacheRep (calls.addCall counts).names (calls.addCall counts).seen := by
  obtain ⟨merged, preserved⟩ := callCache_merge calls counts.keys valid
  refine ⟨?_, preserved⟩
  rw [WordHeuristicCallSet.addCall, merged, heuMergeCall,
    heuristicCountMap_keyProjection, addCall]
  apply (sptEqThm _ _ ⟨sptWfUnion _ _
    ⟨sptWfFromAList _, by rw [sptWfMap]; exact heuristicCountMap_wf _⟩,
    sptWfUnion _ _
    ⟨by rw [sptWfMap]; exact heuristicCountMap_wf _, sptWfFromAList _⟩⟩).mpr
  intro key
  simp only [sptLookup_sptUnion]
  cases sptLookup key (stackNamesTree calls.names) <;>
    cases sptLookup key (sptMap (fun _ => ()) (heuristicCountMapToNative counts)) <;> rfl

end Flapjack.WordAlloc
