import Flapjack.Compiler.Backend.RegAlloc.ProductionStateRelation
import Flapjack.Compiler.Backend.RegAlloc.ProductionAdjacencyCache
import Flapjack.Compiler.Backend.RegAlloc.Initialization

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc

/-- Direct constant arrays represent the complete native REPLICATE list;
there is no representation, validity or successful initialization premise. -/
theorem filled_representsHOLNodeList {α : Type u} (count : Nat) (value : α) :
    CakeNodeMap.RepresentsHOLNodeList (CakeNodeMap.filled count value)
      (List.replicate count value) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [CakeNodeMap.filled]
  · intro node bound
    have bounded : node < count := by simpa using bound
    simp [CakeNodeMap.filled, CakeNodeMap.get, bounded]

/-- The executed constant-array constructor has precisely the complete native
lookup domain, including rejection outside that domain. -/
theorem filled_get {α : Type u} (count : Nat) (value : α) (node : Nat) :
    (CakeNodeMap.filled count value).get node =
      if node < count then some value else none := by
  by_cases bound : node < count <;>
    simp [CakeNodeMap.filled, CakeNodeMap.get, bound, cakeMapLookup, lookupNatInfo]

/-- The actual allocator initializer now has the exact three native scalar
array seeds from reg_alloc_aux/run_ira_state: full zero degree/parent arrays
and a full false move-related array. The independently proved adjacency cache
certificate is retained. This is partial initializer correspondence, not a
claim about native graph/tag construction or the whole phase machine. -/
theorem cakeInitRaStateFromBij_scalarSeed (bij : CakeNodeBijection)
    (tree : WordClashTree) (forced : List (Nat × Nat)) (stackOnly : List Nat) :
    CakeNodeMap.RepresentsHOLNodeList
        (cakeInitRaStateFromBij bij tree forced stackOnly).degrees
        (List.replicate bij.nextNode 0) ∧
      CakeNodeMap.RepresentsHOLNodeList
        (cakeInitRaStateFromBij bij tree forced stackOnly).coalesced
        (List.replicate bij.nextNode 0) ∧
      CakeNodeMap.RepresentsHOLNodeList
        (cakeInitRaStateFromBij bij tree forced stackOnly).moveRelated
        (List.replicate bij.nextNode false) ∧
      (cakeInitRaStateFromBij bij tree forced stackOnly).failure = none ∧
      ProductionAdjacencyCacheSound (cakeInitRaStateFromBij bij tree forced stackOnly) := by
  exact ⟨filled_representsHOLNodeList _ _, filled_representsHOLNodeList _ _,
    filled_representsHOLNodeList _ _, rfl, cakeInitRaStateFromBij_adjacencyCache _ _ _ _⟩

/-- All actual degree, parent and move-related lookups have the same complete
native initial domain. The expected values are derived, not assumed. -/
theorem cakeInitRaStateFromBij_scalarLookup (bij : CakeNodeBijection)
    (tree : WordClashTree) (forced : List (Nat × Nat)) (stackOnly : List Nat)
    (node : Nat) :
    (cakeInitRaStateFromBij bij tree forced stackOnly).degrees.get node =
        (if node < bij.nextNode then some 0 else none) ∧
      (cakeInitRaStateFromBij bij tree forced stackOnly).coalesced.get node =
        (if node < bij.nextNode then some 0 else none) ∧
      (cakeInitRaStateFromBij bij tree forced stackOnly).moveRelated.get node =
        (if node < bij.nextNode then some false else none) := by
  exact ⟨filled_get _ _ _, filled_get _ _ _, filled_get _ _ _⟩

end Flapjack.RegAlloc
