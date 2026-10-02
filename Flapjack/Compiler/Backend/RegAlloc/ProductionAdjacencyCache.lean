import Flapjack.Compiler.Backend.RegAlloc.ProductionStateRelation
import Std.Data.TreeSet.Lemmas

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc

/-- The materialized descending adjacency list preserves every set membership
query. This is the actual production TreeSet/list conversion, not a HOL graph
correctness theorem or a claim about adjacency iteration order. -/
theorem cakeAdjSetList_membership (neighbours : Std.TreeSet Nat) (node : Nat) :
    decide (node ∈ cakeAdjSetList neighbours) = neighbours.contains node := by
  simp [cakeAdjSetList, ← Std.TreeSet.contains_toList]

/-- The actual mapValues materialization preserves cache membership at every
node key, including missing and out-of-dimension extension keys. No valid-map,
dimension or desired-lookup premise is assumed. -/
theorem productionAdjacencyMap_membership (cache : CakeNodeMap (Std.TreeSet Nat))
    (node neighbour : Nat) :
    (cache.get node).map (fun neighbours => neighbours.contains neighbour) =
      ((cache.mapValues cakeAdjSetList).get node).map
        (fun neighbours => decide (neighbour ∈ neighbours)) := by
  rw [CakeNodeMap.get_mapValues]
  cases cache.get node <;> simp [cakeAdjSetList_membership]

/-- The real cached initializer satisfies the complete cache/list query
invariant for every bijection, source tree, forced list and stack-only list.
This does not establish native initRaState equivalence or phase correctness. -/
theorem cakeInitRaStateFromBij_adjacencyCache (bij : CakeNodeBijection)
    (tree : WordClashTree) (forced : List (Nat × Nat)) (stackOnly : List Nat) :
    ProductionAdjacencyCacheSound (cakeInitRaStateFromBij bij tree forced stackOnly) := by
  unfold cakeInitRaStateFromBij ProductionAdjacencyCacheSound
  dsimp only
  intro node neighbour
  exact productionAdjacencyMap_membership _ node neighbour

/-- The executed cached adjacency query agrees with the actual materialized
list membership, including missing node slots. This is a caller equation,
not an assumed source graph or a successful allocation premise. -/
theorem cakeInitRaStateFromBij_adjMem (bij : CakeNodeBijection)
    (tree : WordClashTree) (forced : List (Nat × Nat)) (stackOnly : List Nat)
    (neighbour node : Nat) :
    cakeAdjMem (cakeInitRaStateFromBij bij tree forced stackOnly) neighbour node =
      decide (neighbour ∈ cakeAdjSub
        (cakeInitRaStateFromBij bij tree forced stackOnly).adjLists node) := by
  unfold cakeInitRaStateFromBij cakeAdjMem cakeAdjSub
  dsimp only
  rw [CakeNodeMap.get_mapValues]
  generalize (cakeExtendGraphSet _ forced _).get node = neighbours
  cases neighbours <;> simp [cakeAdjSetList_membership]

/-- Public initializer wrapper inherits the actual cache certificate. -/
theorem cakeInitRaState_adjacencyCache (tree : WordClashTree)
    (forced : List (Nat × Nat)) (stackOnly : List Nat) :
    ProductionAdjacencyCacheSound (cakeInitRaState tree forced stackOnly) :=
  cakeInitRaStateFromBij_adjacencyCache _ tree forced stackOnly

end Flapjack.RegAlloc
