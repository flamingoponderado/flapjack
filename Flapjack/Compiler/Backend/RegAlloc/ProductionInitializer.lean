import Flapjack.Compiler.Backend.RegAlloc.ProductionInitDomain
import Flapjack.Compiler.Backend.RegAlloc.ProductionInitialSeed
import Flapjack.Compiler.Backend.RegAlloc.Proofs.CliqueSuccess

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc

/-- The literal input seed supplied by original reg_alloc_aux to run_ira_state:
present Atemp tag slots, empty adjacency rows, zero degree/parent slots and
false move slots. Untagged specialization of the already ported native runner;
this is not a complete port of reg_alloc_aux. -/
def initializerIraSeed (dimension : Nat) : IraState :=
  { adj_ls := (dimension, []), node_tag := (dimension, .Atemp)
    degrees := (dimension, 0), dim := dimension, simp_wl := [], spill_wl := []
    freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := []
    coalesced := (dimension, 0), move_related := (dimension, false), stack := [] }

/-- Complete native state obtained by expanding the actual original runner
seed. Every field is retained, including the original Atemp tag value.
Untagged runner specialization for the executed initializer correspondence. -/
def initializerNativeSeed (dimension : Nat) : State :=
  { adj_ls := List.replicate dimension [], node_tag := List.replicate dimension .Atemp
    degrees := List.replicate dimension 0, dim := dimension
    simp_wl := [], spill_wl := [], freeze_wl := []
    avail_moves_wl := [], unavail_moves_wl := []
    coalesced := List.replicate dimension 0, move_related := List.replicate dimension false
    stack := [] }

/-- Original runner expansion, with no invariant or successful computation
assumption. Untagged concrete input specialization; arbitrary exceptions and
zero dimension are preserved. -/
theorem runInitializerSeed_eq {value exception : Type}
    (computation : Translator.Monadic.MonadBase.M State value exception) (dimension : Nat) :
    runIraState computation (initializerIraSeed dimension) =
      Translator.Monadic.MonadBase.run computation (initializerNativeSeed dimension) := rfl

private theorem initializerSeed_noEdge (dimension x y : Nat) :
    ¬ hasEdge (initializerNativeSeed dimension).adj_ls x y := by
  intro edge
  have bounded : x < (List.replicate dimension ([] : List Nat)).length := edge.1
  have read := holEl_eq_getElem x (List.replicate dimension ([] : List Nat)) bounded
  have member := edge.2.2
  change y ∈ holEl x (List.replicate dimension ([] : List Nat)) at member
  rw [read] at member
  simp at member

/-- The literal original seed establishes every native allocator invariant,
including the empty graph's ordering and symmetry. No positive dimension
premise is needed. Untagged concrete input-invariant discharge. -/
theorem initializerNativeSeed_good (dimension : Nat) :
    goodRaState (initializerNativeSeed dimension) := by
  have parents : ∀ node ∈ List.replicate dimension 0, node < dimension := by
    intro node member
    obtain ⟨nonempty, equal⟩ := List.mem_replicate.mp member
    subst node
    omega
  have graphBound : ∀ row ∈ List.replicate dimension ([] : List Nat),
      ∀ node ∈ row, node < dimension := by
    intro row member node belongs
    obtain ⟨_, equal⟩ := List.mem_replicate.mp member
    subst row
    contradiction
  have ordered : ∀ row ∈ List.replicate dimension ([] : List Nat), holSorted (· > ·) row := by
    intro row member
    obtain ⟨_, equal⟩ := List.mem_replicate.mp member
    subst row
    simp [holSorted]
  have symmetric : undirected (initializerNativeSeed dimension).adj_ls := by
    intro x y edge
    exact False.elim (initializerSeed_noEdge dimension x y edge)
  refine ⟨by simp [initializerNativeSeed], by simp [initializerNativeSeed],
    by simp [initializerNativeSeed], by simp [initializerNativeSeed],
    by simp [initializerNativeSeed], parents, graphBound, ordered,
    by simp [initializerNativeSeed], by simp [initializerNativeSeed],
    by simp [initializerNativeSeed], by simp [initializerNativeSeed],
    by simp [initializerNativeSeed], symmetric⟩

/-- Production carrier for the original runner seed, with the real cached
empty graph constructor and present native tag/scalar slots. This is proof
infrastructure for the intermediate state; the executed initializer computes
its final tags directly, and their complete overwrite is proved separately. -/
def initializerProductionSeed (dimension : Nat) : CakeRaState :=
  { (CakeRaState.empty dimension) with
    adjLists := (cakeAdjSetMapOfSize dimension).mapValues cakeAdjSetList
    adjSets := some (cakeAdjSetMapOfSize dimension)
    nodeTag := CakeNodeMap.filled dimension .aTemp
    degrees := CakeNodeMap.filled dimension 0
    coalesced := CakeNodeMap.filled dimension 0
    moveRelated := CakeNodeMap.filled dimension false }

/-- The original seed's complete carrier relation is derived from concrete
constructors, not supplied as a caller premise. The real cache/list codec and
every scalar/worklist/failure field are covered. Untagged initializer support. -/
theorem initializerSeed_production (dimension : Nat) :
    ProductionStateRel (initializerNativeSeed dimension) (initializerProductionSeed dimension) := by
  have adjacency : (cakeAdjSetMapOfSize dimension).mapValues cakeAdjSetList =
      CakeNodeMap.filled dimension ([] : List Nat) := by
    have empty : (∅ : Std.TreeSet Nat).toList = [] := rfl
    simp [cakeAdjSetMapOfSize, CakeNodeMap.mapValues, cakeAdjSetList, CakeNodeMap.filled, empty]
  refine {
    adjacency := ?_
    tags := ?_
    degrees := filled_representsHOLNodeList _ _
    parents := filled_representsHOLNodeList _ _
    moveRelated := filled_representsHOLNodeList _ _
    dimension := rfl
    simplify := rfl
    spill := rfl
    freeze := rfl
    availableMoves := rfl
    unavailableMoves := rfl
    stack := rfl
    adjacencyCache := ?_
    failure := rfl }
  · change CakeNodeMap.RepresentsHOLNodeList
      ((cakeAdjSetMapOfSize dimension).mapValues cakeAdjSetList) (List.replicate dimension [])
    rw [adjacency]
    exact filled_representsHOLNodeList _ _
  · simpa [initializerNativeSeed, initializerProductionSeed, Tag.toProduction] using
      filled_representsHOLNodeList dimension (.aTemp : CakeNodeTag)
  · exact productionAdjacencyMap_membership _

/-- Full graph stage from the actual constructed bijection and original
runner seed. Its domain, injectivity and initial Good certificate are derived;
the successful evaluation, resulting Good state and complete production
relation are proved. Untagged real initializer-stage correspondence. -/
theorem initializerGraph_production (tree : WordClashTree) :
    let bij := cakeMkBij tree
    let ta := cakeSpDefaultIndexed (cakeSpDefaultIndex bij.toAllocator)
    let cache := cakeAdjSetMapOfSize bij.nextNode
    ∃ result, mkGraph ta (productionClashTreeToNative tree) [] (initializerNativeSeed bij.nextNode) =
        (.success (cakeMkGraphSet ta tree [] cache).2, result) ∧
      goodRaState result ∧ result.dim = bij.nextNode ∧
      ProductionStateRel result {(initializerProductionSeed bij.nextNode) with
        adjLists := (cakeMkGraphSet ta tree [] cache).1.mapValues cakeAdjSetList
        adjSets := some (cakeMkGraphSet ta tree [] cache).1} := by
  dsimp only
  let dimension := (cakeMkBij tree).nextNode
  let ta := cakeSpDefaultIndexed (cakeSpDefaultIndex (cakeMkBij tree).toAllocator)
  obtain ⟨result, run, length, rel⟩ := mkGraphSet_production ta tree []
    (cakeAdjSetMapOfSize dimension)
    (native := initializerNativeSeed dimension) (production := initializerProductionSeed dimension)
    (initializerSeed_production dimension)
    (by simpa [initializerNativeSeed, dimension, ta] using producedAllocator_graphInputBound tree) (by simp)
  have nameBound : ∀ name, inClashTree (productionClashTreeToNative tree) name →
      ta name < dimension := producedAllocator_name_bound tree
  have injective : ∀ left right, inClashTree (productionClashTreeToNative tree) left →
      inClashTree (productionClashTreeToNative tree) right → ta left = ta right → left = right :=
    producedAllocator_name_injective tree
  obtain ⟨live, goodResult, goodRun, good, clique, frame, rest⟩ := mkGraphSucceeds
    (productionClashTreeToNative tree) ta [] (initializerNativeSeed dimension)
    ⟨initializerNativeSeed_good dimension, nameBound,
      ⟨by simpa [initializerNativeSeed] using nameBound, injective⟩,
      by simp [isClique], by simp, by simp⟩
  have resultEq := congrArg Prod.snd (run.symm.trans goodRun)
  change result = goodResult at resultEq
  subst goodResult
  have dim := congrArg State.dim frame
  refine ⟨result, run, good, ?_, ?_⟩
  · exact dim
  · exact rel

/-- Complete executed initializer/native initRaState correspondence from the
original runner seed and actual produced bijection. Tree-node domains and
injectivity are derived. Forced endpoint bounds are genuine input conditions;
their source-producer discharge remains separately tracked. No desired graph,
tag map, successful evaluation or post-state relation is a premise.
Untagged actual/native correspondence, not a duplicate HOL correctness port. -/
theorem initializer_production (tree : WordClashTree) (forced : List (Nat × Nat)) (stackOnly : List Nat)
    (forcedBounds : ∀ pair ∈ forced,
      cakeSpDefaultIndexed (cakeSpDefaultIndex (cakeMkBij tree).toAllocator) pair.1 < (cakeMkBij tree).nextNode ∧
      cakeSpDefaultIndexed (cakeSpDefaultIndex (cakeMkBij tree).toAllocator) pair.2 < (cakeMkBij tree).nextNode) :
    ∃ result, initRaState (productionClashTreeToNative tree) forced
        (sptFromAList (stackOnly.map (fun name => (name, ()))))
        (mkBij (productionClashTreeToNative tree))
        (initializerNativeSeed (cakeMkBij tree).nextNode) = (.success (), result) ∧
      goodRaState result ∧ ProductionStateRel result (cakeInitRaState tree forced stackOnly) := by
  let bij := cakeMkBij tree
  let ta := cakeSpDefaultIndexed (cakeSpDefaultIndex bij.toAllocator)
  let graph := (cakeMkGraphSet ta tree [] (cakeAdjSetMapOfSize bij.nextNode)).1
  obtain ⟨first, firstRun, firstGood, firstDim, firstRel⟩ := initializerGraph_production tree
  obtain ⟨second, secondRun, secondLength, secondRel⟩ := extendGraphSet_production ta forced graph
    (native := first) (production := initializerProductionSeed bij.nextNode) firstRel (by
      intro pair belongs
      rw [firstGood.1, firstDim]
      exact forcedBounds pair belongs)
  obtain ⟨goodSecond, goodRun, secondGood, secondFrame, rest⟩ := extendGraphSucceeds forced ta first
    ⟨firstGood, by
      intro pair belongs
      rw [firstDim]
      exact forcedBounds pair belongs⟩
  have secondEq := congrArg Prod.snd (secondRun.symm.trans goodRun)
  change second = goodSecond at secondEq
  subst goodSecond
  have secondDim : second.dim = bij.nextNode := (congrArg State.dim secondFrame).trans firstDim
  obtain ⟨result, tagRun, resultGood, tagDim, resultRel⟩ := mkTags_production bij.fromAllocator stackOnly
    secondRel secondGood
  have forwardEq : Flapjack.spDefault (sptFromAList bij.toAllocator) = ta := by
    funext name
    exact (tagDecoder_production bij.toAllocator name).symm
  refine ⟨result, ?_, resultGood, ?_⟩
  · rw [mkBij_production]
    change initRaState (productionClashTreeToNative tree) forced
      (sptFromAList (stackOnly.map (fun name => (name, ()))))
      (sptFromAList bij.toAllocator, sptFromAList bij.fromAllocator, bij.nextNode)
      (initializerNativeSeed bij.nextNode) = _
    simp only [initRaState]
    rw [forwardEq]
    simp only [Translator.Monadic.MonadBase.ignoreBind]
    rw [firstRun]
    rw [secondRun]
    simpa only [secondDim] using tagRun
  · simpa only [cakeInitRaState, cakeInitRaStateFromBij, initializerProductionSeed,
      secondDim, bij, ta, graph] using resultRel

/-- Original-source variant of the complete initializer correspondence.
Both the original clash tree and original stack-only set are reconstructed
exactly by the reviewed codecs. The forced endpoint conditions remain input
domains, with producer discharge tracked separately. Untagged actual/native
initializer infrastructure; this is not whole compiler correctness. -/
theorem initializer_original_production (tree : ClashTree) (wellFormed : NativeClashTreeSetsWf tree)
    (forced : List (Nat × Nat)) (stackOnly : NumSet) (stackWellFormed : sptWf stackOnly = true)
    (forcedBounds : ∀ pair ∈ forced,
      cakeSpDefaultIndexed (cakeSpDefaultIndex (cakeMkBij (nativeClashTreeToProduction tree)).toAllocator)
        pair.1 < (cakeMkBij (nativeClashTreeToProduction tree)).nextNode ∧
      cakeSpDefaultIndexed (cakeSpDefaultIndex (cakeMkBij (nativeClashTreeToProduction tree)).toAllocator)
        pair.2 < (cakeMkBij (nativeClashTreeToProduction tree)).nextNode) :
    ∃ result, initRaState tree forced stackOnly (mkBij tree)
        (initializerNativeSeed (cakeMkBij (nativeClashTreeToProduction tree)).nextNode) = (.success (), result) ∧
      goodRaState result ∧ ProductionStateRel result
        (cakeInitRaState (nativeClashTreeToProduction tree) forced ((sptToAList stackOnly).map Prod.fst)) := by
  have stackRoundtrip : sptFromAList (((sptToAList stackOnly).map Prod.fst).map
      (fun name => (name, ()))) = stackOnly := by
    have reconstructed := clashTreeCodec_roundtrip (.set stackOnly) stackWellFormed
    change ClashTree.set (sptFromAList (((sptToAList stackOnly).map Prod.fst).map
      (fun name => (name, ())))) = ClashTree.set stackOnly at reconstructed
    exact ClashTree.set.inj reconstructed
  simpa only [clashTreeCodec_roundtrip tree wellFormed, stackRoundtrip] using
    initializer_production (nativeClashTreeToProduction tree) forced
      ((sptToAList stackOnly).map Prod.fst) forcedBounds

end Flapjack.RegAlloc
