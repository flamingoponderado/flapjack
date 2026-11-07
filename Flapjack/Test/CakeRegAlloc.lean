import Flapjack.RiscV.CakeRegAlloc
import Flapjack.Compiler.Backend.WordUnreach
import Flapjack.Compiler.Backend.WordCse.ListOrder
import Flapjack.Compiler.Backend.WordCse.RegisterUses
import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
import Flapjack.Compiler.Backend.RegAlloc.ProductionHandledColourReads

/-!
# Cake register-allocation stack-only analysis parity

Mirrors of the `word_alloc$get_stack_only` probe fixtures in
`scripts/hol-probes/get_stack_only_probeScript.sml` (oracle outputs in
`get_stack_only_probe.out`, from
`cakeml/compiler/backend/word_allocScript.sml:1741-1789`) and of the
`reg_alloc$mk_bij` / `list_remap` fixtures in
`scripts/hol-probes/mk_bij_probeScript.sml` (oracle outputs in
`mk_bij_probe.out`, from
`cakeml/compiler/backend/reg_alloc/reg_allocScript.sml:1096-1130`).

Bead `flapjack-pxn.8.5.14.1.3` (frame occupancy and allocator temporary
slots), driver slices 1 and 3.  The forced-pair analysis (`get_forced`) is
covered by `Flapjack.Test.CakeForcedParity` on the coordinator side.
-/

namespace Flapjack.Test.CakeRegAlloc

open Flapjack.RiscV.CakeRegAlloc

/-! HOL `st_ex_MAP_node_tag_sub` reads the node list with `EL` only for
    indices below its length.  The dense CakeNodeMap bridge agrees at the
    first and last valid indices and documents Lean's `none` outside the
    represented range. -/
def cakeNodeMapHolListLookupGuard : Bool :=
  let nodes : List Nat := [7, 11, 13]
  CakeNodeMap.get (CakeNodeMap.ofList nodes) 0 == some 7 &&
    CakeNodeMap.get (CakeNodeMap.ofList nodes) 2 == some 13 &&
    CakeNodeMap.get (CakeNodeMap.ofList nodes) 3 == none &&
    CakeNodeMap.get (CakeNodeMap.ofList ([] : List Nat)) 0 == none

#guard cakeNodeMapHolListLookupGuard

/-! The same-index and non-updated-index observations mirror bounded HOL
    `LUPDATE`.  Persistent Lean updates retain the original value, preserve
    array length, and explicitly expose the extra outside-map behavior. -/
def cakeNodeMapHolListUpdateGuard : Bool :=
  let nodes : List Nat := [7, 11, 13]
  let original := CakeNodeMap.ofList nodes
  let updated := CakeNodeMap.set original 1 99
  let sibling := CakeNodeMap.set original 1 77
  let extended := CakeNodeMap.set original 3 99
  CakeNodeMap.get updated 1 == some 99 &&
    CakeNodeMap.get sibling 1 == some 77 &&
    CakeNodeMap.get updated 0 == some 7 &&
    CakeNodeMap.get original 1 == some 11 &&
    updated.slots.size == nodes.length &&
    CakeNodeMap.get extended 3 == some 99 &&
    extended.slots.size == nodes.length

#guard cakeNodeMapHolListUpdateGuard

/-! The production `mapValues` rebuilds every node value.  It preserves the
    checked dense node-list representation, mapping the HOL field pointwise,
    which extends the `ofList`/`set` laws to the value-rebuilding operation
    used by production node-tag fields. -/
def cakeNodeMapMapValuesGuard : Bool :=
  let nodes : List Nat := [7, 11, 13]
  let mapped := CakeNodeMap.mapValues (fun n => n + 1) (CakeNodeMap.ofList nodes)
  mapped.get 0 == some 8 && mapped.get 2 == some 14 &&
    mapped.get 3 == none && mapped.slots.size == nodes.length

#guard cakeNodeMapMapValuesGuard

example :
    CakeNodeMap.RepresentsHOLNodeList
      (CakeNodeMap.mapValues (fun n : Nat => n + 1)
        (CakeNodeMap.ofList [7, 11, 13]))
      [8, 12, 14] := by
  simpa using CakeNodeMap.mapValues_representsHOLNodeList (fun n : Nat => n + 1)
    (CakeNodeMap.ofList [7, 11, 13]) [7, 11, 13]
    (CakeNodeMap.ofList_representsHOLNodeList [7, 11, 13])

example (m : CakeNodeMap Nat) (i : Nat) :
    (CakeNodeMap.mapValues (fun n : Nat => n + 1) m).get i =
      (m.get i).map (fun n => n + 1) := by
  exact CakeNodeMap.get_mapValues (fun n : Nat => n + 1) m i

/-! The production `ofNatInfoMap` fold builds a node field from a HOL
    association list.  Fed the dense indexed list of a HOL node field it agrees
    with the first-binding lookup and rebuilds exactly the same dense field as
    `ofList`; an out-of-range key stays in the extension map but is still read
    back by `get`. -/
def cakeNodeMapOfNatInfoMapGuard : Bool :=
  let values : List Nat := [7, 11, 13]
  let indexed := values.mapIdx (fun i v => (i, v))
  let built := CakeNodeMap.ofNatInfoMap values.length indexed
  let dense := CakeNodeMap.ofList values
  let extended := CakeNodeMap.ofNatInfoMap values.length (indexed ++ [(5, 99)])
  built.get 0 == some 7 && built.get 1 == some 11 &&
    built.get 2 == some 13 && built.get 3 == none &&
    built.slots.size == values.length && built.outside == [] &&
    (List.range values.length).all (fun i => built.get i == dense.get i) &&
    extended.get 5 == some 99 && extended.outside == [(5, 99)]

#guard cakeNodeMapOfNatInfoMapGuard

example :
    CakeNodeMap.RepresentsHOLNodeList
      (CakeNodeMap.ofNatInfoMap 3 ([7, 11, 13].mapIdx (fun i v => (i, v))))
      [7, 11, 13] :=
  CakeNodeMap.ofNatInfoMap_mapIdx_representsHOLNodeList [7, 11, 13]

example (m : Flapjack.NatInfoMap Nat) (i : Nat) :
    CakeNodeMap.get (CakeNodeMap.ofNatInfoMap 4 m) i =
      Flapjack.RiscV.CakeRegAlloc.cakeMapLookup m i :=
  CakeNodeMap.get_ofNatInfoMap 4 m i

example :
    CakeNodeMap.get
      (CakeNodeMap.ofNatInfoMap 3 ([7, 11, 13].mapIdx (fun i v => (i, v)))) 1 =
        some 11 := by
  rw [CakeNodeMap.get_ofNatInfoMap]
  exact CakeNodeMap.lookupNatInfo_mapIdx_add [7, 11, 13] 0 1 (by decide)

/-! The production `toNatInfoMap` readback reconstructs the HOL indexed node
    list from the array field, agrees with `get` at every index (in range and
    past the dense dimension), and inverts `ofNatInfoMap`'s dense embedding. -/
def cakeNodeMapToNatInfoMapGuard : Bool :=
  let values : List Nat := [7, 11, 13]
  let dense := CakeNodeMap.ofList values
  dense.toNatInfoMap == values.mapIdx (fun i v => (i, v)) &&
    Flapjack.lookupNatInfo 0 dense.toNatInfoMap == dense.get 0 &&
    Flapjack.lookupNatInfo 1 dense.toNatInfoMap == dense.get 1 &&
    Flapjack.lookupNatInfo 3 dense.toNatInfoMap == dense.get 3

#guard cakeNodeMapToNatInfoMapGuard

example :
    (CakeNodeMap.ofList [7, 11, 13]).toNatInfoMap =
      [7, 11, 13].mapIdx (fun i v => (i, v)) :=
  CakeNodeMap.toNatInfoMap_eq_mapIdx (CakeNodeMap.ofList [7, 11, 13]) [7, 11, 13]
    (CakeNodeMap.ofList_representsHOLNodeList [7, 11, 13])

example (i : Nat) :
    Flapjack.lookupNatInfo i (CakeNodeMap.ofList [7, 11, 13]).toNatInfoMap =
      (CakeNodeMap.ofList [7, 11, 13]).get i :=
  CakeNodeMap.lookupNatInfo_toNatInfoMap (CakeNodeMap.ofList [7, 11, 13])
    [7, 11, 13] (CakeNodeMap.ofList_representsHOLNodeList [7, 11, 13]) i

example :
    CakeNodeMap.RepresentsHOLNodeList
      (CakeNodeMap.ofNatInfoMap 3 (CakeNodeMap.ofList [7, 11, 13]).toNatInfoMap)
      [7, 11, 13] :=
  CakeNodeMap.toNatInfoMap_representsHOLNodeList (CakeNodeMap.ofList [7, 11, 13])
    [7, 11, 13] (CakeNodeMap.ofList_representsHOLNodeList [7, 11, 13])

example :
    CakeNodeMap.RepresentsHOLNodeList
      (CakeNodeMap.set (CakeNodeMap.ofList [7, 11, 13]) 1 99)
      [7, 99, 13] := by
  have h := CakeNodeMap.set_representsHOLNodeList
    (CakeNodeMap.ofList [7, 11, 13]) [7, 11, 13]
    (CakeNodeMap.ofList_representsHOLNodeList [7, 11, 13]) 1 99 (by decide)
  simpa using h

example :
    CakeNodeMap.RepresentsHOLNodeList
      (CakeNodeMap.set
        (CakeNodeMap.set (CakeNodeMap.ofList [7, 11, 13]) 1 99) 2 88)
      [7, 99, 88] := by
  have h₁ : CakeNodeMap.RepresentsHOLNodeList
      (CakeNodeMap.set (CakeNodeMap.ofList [7, 11, 13]) 1 99)
      [7, 99, 13] := by
    exact (show CakeNodeMap.RepresentsHOLNodeList
      (CakeNodeMap.set (CakeNodeMap.ofList [7, 11, 13]) 1 99)
      (List.set [7, 11, 13] 1 99) from
        CakeNodeMap.set_representsHOLNodeList _ _
          (CakeNodeMap.ofList_representsHOLNodeList _) _ _ (by decide))
  have h₂ := CakeNodeMap.set_representsHOLNodeList
    (CakeNodeMap.set (CakeNodeMap.ofList [7, 11, 13]) 1 99)
    [7, 99, 13] h₁ 2 88 (by decide)
  simpa using h₂

example : CakeNodeMap.get (CakeNodeMap.ofList [7, 11, 13]) 0 = some 7 := by
  exact CakeNodeMap.get_ofList_of_lt _ _ (by decide)

example : CakeNodeMap.get (CakeNodeMap.ofList [7, 11, 13]) 2 = some 13 := by
  exact CakeNodeMap.get_ofList_of_lt _ _ (by decide)

example : CakeNodeMap.get (CakeNodeMap.ofList [7, 11, 13]) 3 = none := by
  exact CakeNodeMap.get_ofList_of_ge _ _ (by decide)

example : CakeNodeMap.get (CakeNodeMap.ofList ([] : List Nat)) 0 = none := by
  exact CakeNodeMap.get_ofList_empty _

example :
    CakeNodeMap.get (CakeNodeMap.set (CakeNodeMap.ofList [7, 11, 13]) 1 99) 1 =
      some 99 := by
  exact CakeNodeMap.get_set_ofList_same _ _ _ (by decide)

example :
    CakeNodeMap.get (CakeNodeMap.set (CakeNodeMap.ofList [7, 11, 13]) 1 99) 0 =
      some 7 := by
  exact CakeNodeMap.get_set_ofList_other _ _ _ _ (by decide) (by decide)
    (by decide)

example :
    (CakeNodeMap.set (CakeNodeMap.ofList [7, 11, 13]) 1 99).slots.size = 3 := by
  simpa using CakeNodeMap.set_ofList_slots_size [7, 11, 13] 1 99

example :
    CakeNodeMap.get (CakeNodeMap.set (CakeNodeMap.ofList [7, 11, 13]) 3 99) 3 =
      some 99 := by
  exact CakeNodeMap.get_set_ofList_outside _ _ _ (by decide)

/- The TreeSet graph accumulator must materialize the same descending Cake
   adjacency lists as the reference list insertion path. -/
def graphSetAccumulatorGuard : Bool :=
  let tree : WordClashTree :=
    .seq
      (.delta [1, 3] [2, 4])
      (.branch (some [5, 6])
        (.set [7, 8, 7])
        (.delta [9] [1, 8]))
  let bij := cakeMkBij tree
  let sourceIndex := cakeSpDefaultIndex bij.toAllocator
  let ta := cakeSpDefaultIndexed sourceIndex
  let (reference, _) := cakeMkGraph ta tree [] (CakeNodeMap.ofSize bij.nextNode)
  let reference := cakeExtendGraph ta [(1, 9), (8, 2)] reference
  let (accumulated, _) :=
    cakeMkGraphSet ta tree [] (cakeAdjSetMapOfSize bij.nextNode)
  let accumulated := cakeExtendGraphSet ta [(1, 9), (8, 2)] accumulated
  reference.toNatInfoMap == (accumulated.mapValues cakeAdjSetList).toNatInfoMap

#guard graphSetAccumulatorGuard

def cliqueSetAccumulatorGuard : Bool :=
  let live := [1, 3, 5, 7]
  let initial := cakeAdjSetMapOfSize 8
  (cakeCliqueInsertEdgeSetFast live initial).toNatInfoMap ==
    (cakeCliqueInsertEdgeSet live initial).toNatInfoMap

#guard cliqueSetAccumulatorGuard

def extendCliqueSetAccumulatorGuard : Bool :=
  let newNames := [1, 4, 1, 3]
  let live := [2, 4, 6]
  let initial := cakeAdjSetMapOfSize 8
  let fast := cakeExtendCliqueSetFast newNames live initial
  let reference := cakeExtendCliqueSetReference newNames live initial
  fast.2 == reference.2 && fast.1.toNatInfoMap == reference.1.toNatInfoMap

#guard extendCliqueSetAccumulatorGuard

def extendCliqueSetBatchGuard : Bool :=
  let newNames := [9, 4, 9, 2, 7]
  let live := [2, 4, 6, 4]
  let initial := cakeAdjSetMapOfSize 12
  let seeded := cakeInsertEdgeSet 1 6 initial
  let batch := cakeExtendCliqueSetBatch newNames live seeded
  let reference := cakeExtendCliqueSetReference newNames live seeded
  batch.2 == reference.2 && batch.1.toNatInfoMap == reference.1.toNatInfoMap

#guard extendCliqueSetBatchGuard

def extendCliqueSetBatchEmptyLiveGuard : Bool :=
  let newNames := [9, 9, 4, 2]
  let live := []
  let initial := cakeAdjSetMapOfSize 12
  let seeded := cakeInsertEdgeSet 1 6 initial
  let batch := cakeExtendCliqueSetBatch newNames live seeded
  let reference := cakeExtendCliqueSetReference newNames live seeded
  batch.2 == reference.2 && batch.1.toNatInfoMap == reference.1.toNatInfoMap

#guard extendCliqueSetBatchEmptyLiveGuard

def extendCliqueSetBatchOverlappingCliqueGuard : Bool :=
  let newNames := [1, 4, 1, 3, 8, 3]
  let live := [2, 4, 6, 4, 8]
  let initial := cakeAdjSetMapOfSize 12
  let seeded := cakeInsertEdgeSet 0 11
    (cakeInsertEdgeSet 5 6 initial)
  let batch := cakeExtendCliqueSetBatch newNames live seeded
  let reference := cakeExtendCliqueSetReference newNames live seeded
  batch.2 == reference.2 && batch.1.toNatInfoMap == reference.1.toNatInfoMap

#guard extendCliqueSetBatchOverlappingCliqueGuard

def indexedAdjacencyMembershipGuard : Bool :=
  let tree : WordClashTree := .delta [1, 3] [2, 4]
  let bij := cakeMkBij tree
  let state := cakeInitRaStateFromBij bij tree [] []
  (List.range state.dim).all (fun x =>
    (List.range state.dim).all (fun y =>
      cakeAdjMem state x y == cakeSortedMem x (cakeAdjSub state.adjLists y)))

#guard indexedAdjacencyMembershipGuard

def filterReversedGuard : Bool :=
  filterReversed (fun x : Nat => x % 2 = 1) [1, 2, 3, 4, 5, 6] = [5, 3, 1]

#guard filterReversedGuard

/-- Canonical form for comparing node bijections with the probed sptree
    outputs: both maps sorted by key. -/
def sortBijectionMaps (bijection : CakeNodeBijection) :
    List (Nat × Nat) × List (Nat × Nat) :=
  (bijection.toAllocator.mergeSort (fun a b => a.1 < b.1),
   bijection.fromAllocator.mergeSort (fun a b => a.1 < b.1))

/-- Reads are remapped before writes: 2, 3 then 1. -/
def bijDeltaBasicGuard : Bool :=
  sortBijectionMaps (cakeMkBij (.delta [1] [2, 3] : WordClashTree)) =
    ([(1, 2), (2, 0), (3, 1)], [(0, 2), (1, 3), (2, 1)]) &&
  (cakeMkBij (.delta [1] [2, 3] : WordClashTree)).nextNode = 3

/-- Already-mapped names are skipped: the write of 2 adds no node. -/
def bijDeltaDedupGuard : Bool :=
  sortBijectionMaps (cakeMkBij (.delta [2] [2, 3] : WordClashTree)) =
    ([(2, 0), (3, 1)], [(0, 2), (1, 3)]) &&
  (cakeMkBij (.delta [2] [2, 3] : WordClashTree)).nextNode = 2

/-- `Seq` remaps the right subtree first: 7 before 5. -/
def bijSeqOrderGuard : Bool :=
  sortBijectionMaps (cakeMkBij
    (.seq (.delta [] [5] : WordClashTree) (.delta [] [7] : WordClashTree))) =
    ([(5, 1), (7, 0)], [(0, 7), (1, 5)])

/-- `Branch` remaps the left subtree, then the right subtree. -/
def bijBranchOrderGuard : Bool :=
  sortBijectionMaps (cakeMkBij
    (.branch none (.delta [] [9] : WordClashTree) (.delta [] [11] : WordClashTree))) =
    ([(9, 0), (11, 1)], [(0, 9), (1, 11)])

/-- The optional live set is remapped after both subtrees. -/
def bijBranchLiveGuard : Bool :=
  sortBijectionMaps (cakeMkBij
    (.branch (some [13]) (.delta [] [9] : WordClashTree)
      (.delta [] [11] : WordClashTree))) =
    ([(9, 0), (11, 1), (13, 2)], [(0, 9), (1, 11), (2, 13)]) &&
  (cakeMkBij
    (.branch (some [13]) (.delta [] [9] : WordClashTree)
      (.delta [] [11] : WordClashTree))).nextNode = 3

/-- `Set` remaps its fixed name list; the sptree original always walks
    ascending keys, so an unsorted list is normalized at the boundary. -/
def bijSetGuard : Bool :=
  sortBijectionMaps (cakeMkBij (.set [3, 4] : WordClashTree)) =
    ([(3, 0), (4, 1)], [(0, 3), (1, 4)])

/-- Unsorted `Set` input still numbers ascending, matching the sptree
    iteration of the original (cake `Set` has no order to violate). -/
def bijSetUnsortedGuard : Bool :=
  sortBijectionMaps (cakeMkBij (.set [4, 3] : WordClashTree)) =
    ([(3, 0), (4, 1)], [(0, 3), (1, 4)])

/-- Composite tree: the branch (with live set) runs first, then the delta. -/
def bijCompositeGuard : Bool :=
  sortBijectionMaps (cakeMkBij
    (.seq (.delta [1] [2] : WordClashTree)
      (.branch (some [6]) (.delta [] [4] : WordClashTree)
        (.delta [] [5] : WordClashTree)))) =
    ([(1, 4), (2, 3), (4, 0), (5, 1), (6, 2)],
     [(0, 4), (1, 5), (2, 6), (3, 2), (4, 1)]) &&
  (cakeMkBij
    (.seq (.delta [1] [2] : WordClashTree)
      (.branch (some [6]) (.delta [] [4] : WordClashTree)
        (.delta [] [5] : WordClashTree)))).nextNode = 5

/- The indexed builder is only an implementation optimization; its public
   maps and numbering must remain identical to the direct Cake-shaped walk. -/
def bijIndexedBuilderParityGuard : Bool :=
  let trees : List WordClashTree :=
    [.delta [1] [2, 3],
     .branch (some [13]) (.delta [] [9]) (.delta [] [11]),
     .seq (.delta [1] [2])
       (.branch (some [6]) (.delta [] [4]) (.delta [] [5]))]
  trees.all (fun tree =>
    let reference := cakeMkBijAux tree
      { toAllocator := [], fromAllocator := [], nextNode := 0 }
    let indexed := cakeMkBij tree
    indexed.toAllocator == reference.toAllocator &&
      indexed.fromAllocator == reference.fromAllocator &&
      indexed.nextNode == reference.nextNode)

#guard bijIndexedBuilderParityGuard

/- The hot-path source index must preserve the Cake association-list lookup,
   including the zero fallback for a name absent from the bijection. -/
def allocatorIndexLookupGuard : Bool :=
  let entries : NatInfoMap Nat := [(9, 4), (1, 2), (17, 6)]
  let index := cakeAllocatorIndex entries
  cakeAllocatorIndexLookup index 9 = 4 &&
    cakeAllocatorIndexLookup index 1 = 2 &&
    cakeAllocatorIndexLookup index 17 = 6 &&
    cakeAllocatorIndexLookup index 99 = 0

#guard allocatorIndexLookupGuard

/- Cake's association-list lookup is first-binding.  The allocator index must
   preserve that result even when presented with a duplicate-key map. -/
def allocatorIndexFirstBindingGuard : Bool :=
  let entries : NatInfoMap Nat := [(9, 4), (9, 6)]
  let index := cakeAllocatorIndex entries
  cakeAllocatorIndexLookup index 9 == 4

#guard allocatorIndexFirstBindingGuard

/- The graph/tag hot path uses an index only as a lookup acceleration; its
   default and physical-register fallbacks must remain Cake's `sp_default`. -/
def spDefaultIndexParityGuard : Bool :=
  let entries : NatInfoMap Nat := [(9, 4), (1, 2), (17, 6)]
  let index := cakeSpDefaultIndex entries
  cakeSpDefaultIndexed index 9 == Flapjack.RiscV.CakeAlloc.spDefault entries 9 &&
    cakeSpDefaultIndexed index 1 == Flapjack.RiscV.CakeAlloc.spDefault entries 1 &&
    cakeSpDefaultIndexed index 17 == Flapjack.RiscV.CakeAlloc.spDefault entries 17 &&
    cakeSpDefaultIndexed index 8 == Flapjack.RiscV.CakeAlloc.spDefault entries 8 &&
    cakeSpDefaultIndexed index 7 == Flapjack.RiscV.CakeAlloc.spDefault entries 7

/- Cake's association-list lookup is first-binding.  The indexed accelerator
   must preserve that result if a source map contains a duplicate key. -/
def spDefaultIndexFirstBindingGuard : Bool :=
  let entries : NatInfoMap Nat := [(9, 4), (9, 6)]
  let index := cakeSpDefaultIndex entries
  cakeSpDefaultIndexed index 9 == Flapjack.RiscV.CakeAlloc.spDefault entries 9

#guard spDefaultIndexFirstBindingGuard
#guard spDefaultIndexParityGuard

def extractColorOrderGuard : Bool :=
  let tree : WordClashTree := .delta [9, 1] [17]
  let bij := cakeMkBij tree
  let state := cakeInitRaState tree [] []
  cakeExtractColor state bij.toAllocator ==
    [(1, 0), (9, 0), (17, 0)]

#guard extractColorOrderGuard

/- Cake's `assign_Atemp_tag` removes colours used by fixed neighbours before
   applying the preference oracle. A fixed neighbour at colour 1 forces node
   0 to choose colour 0. -/
def assignAtempFixedNeighbourGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 3 with
      adjLists := CakeNodeMap.ofNatInfoMap 3 [(0, [1]), (1, [0])]
      nodeTag := CakeNodeMap.ofNatInfoMap 3 [(0, .aTemp), (1, .fixed 1)] }
  let out := cakeAssignAtempTag 3 (fun _ _ _ => none) 0 state
  out.nodeTag.get 0 == some (.fixed 0)

#guard assignAtempFixedNeighbourGuard

/- Cake's `assign_Stemp_tag` assigns an unbound stack colour at or above k.
   A fixed neighbour at colour 2 forces the first available stack colour to 3
   when k=2. -/
def assignStempUnboundColourGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 3 with
      adjLists := CakeNodeMap.ofNatInfoMap 3 [(0, [1]), (1, [0])]
      nodeTag := CakeNodeMap.ofNatInfoMap 3 [(0, .sTemp), (1, .fixed 2)] }
  let out := cakeAssignStempTag 2 (fun _ _ _ => none) 0 state
  out.nodeTag.get 0 == some (.fixed 3)

#guard assignStempUnboundColourGuard

/- Cake's `assign_Atemps` consumes the filtered heuristic list before its
   full in-dimension pass. With no edges and k=2, all remaining Atemps take
   the first available colour, preserving Cake's traversal order. -/
def assignAtempsHeuristicThenRangeGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 3 with
      nodeTag := CakeNodeMap.ofNatInfoMap 3
        [(0, .aTemp), (1, .aTemp), (2, .aTemp)] }
  let out := cakeAssignAtemps 2 [1] (fun _ _ _ => none) state
  out.nodeTag.get 0 == some (.fixed 0) &&
    out.nodeTag.get 1 == some (.fixed 0) &&
    out.nodeTag.get 2 == some (.fixed 0)

#guard assignAtempsHeuristicThenRangeGuard

/- Cake's `sorted_insert`/`sorted_mem` maintain descending adjacency lists,
   skip duplicate insertion, and stop membership search at the passed key. -/
def sortedInsertMemGuard : Bool :=
  cakeSortedInsert 6 [] == [6] &&
    cakeSortedInsert 5 [7, 4, 2] == [7, 5, 4, 2] &&
    cakeSortedInsert 4 [7, 4, 2] == [7, 4, 2] &&
    cakeSortedInsert 1 [7, 4, 2] == [7, 4, 2, 1] &&
    cakeSortedMem 4 [7, 4, 2] &&
    !cakeSortedMem 5 [7, 4, 2] &&
    !cakeSortedMem 1 [7, 4, 2] &&
    cakeSortedMem 7 [7, 4, 2]

#guard sortedInsertMemGuard

/- Cake's `first_match_col` scans variables in order, ignores non-fixed tags,
   and returns the first fixed neighbour whose colour is in the candidates. -/
def firstMatchColGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 8 with
      nodeTag := CakeNodeMap.ofNatInfoMap 8
        [(1, .fixed 3), (2, .aTemp), (3, .fixed 5), (4, .fixed 7)] }
  cakeFirstMatchCol state [5, 7] [1, 2, 3, 4] == some 5 &&
    cakeFirstMatchCol state [2] [1, 3, 4] == none &&
    -- A missing lookup stops the handled preference, even when a later
    -- partner would match. Cover both a missing slot and an outside index.
    cakeFirstMatchCol state [5] [0, 3] == none &&
    cakeFirstMatchCol state [5] [8, 3] == none

#guard firstMatchColGuard

-- Exact S0 from reg_alloc_colouring_probeScript.sml. The original rows
-- fmc_oob_before_match and fmc_handled_oob_before_match distinguish an
-- immediate failed lookup from incorrectly scanning on to Fixed 0.
private def firstMatchOracleState : Flapjack.RegAlloc.State :=
  { adj_ls := [[1], [0, 2], [1]], node_tag := [.Fixed 0, .Atemp, .Stemp]
    degrees := [1, 2, 1], dim := 3, simp_wl := [], spill_wl := [], freeze_wl := []
    avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 2]
    move_related := [false, false, false], stack := [] }

example : Flapjack.RegAlloc.firstMatchCol [0] [9, 0] firstMatchOracleState =
    (.failure .Subscript, firstMatchOracleState) := by decide

example : Flapjack.RegAlloc.handleSubscript
    (Flapjack.RegAlloc.firstMatchCol [0] [9, 0])
    (Flapjack.Translator.Monadic.MonadBase.ret none) firstMatchOracleState =
    (.success none, firstMatchOracleState) := by decide

example : cakeFirstMatchCol firstMatchOracleState.toProduction [0] [9, 0] = none := by
  have nativeRun : Flapjack.RegAlloc.handleSubscript
      (Flapjack.RegAlloc.firstMatchCol [0] [9, 0])
      (Flapjack.Translator.Monadic.MonadBase.ret none) firstMatchOracleState =
      (.success none, firstMatchOracleState) := by decide
  have correspondence := Flapjack.RegAlloc.handledFirstMatchCol_production [0] [9, 0]
    firstMatchOracleState.toProduction_rel
  rw [nativeRun] at correspondence
  exact (Flapjack.Translator.Monadic.MonadBase.Exc.success.inj
    (congrArg Prod.fst correspondence)).symm

/- Cake's `assign_Stemps` visits every node in ascending range order and
   assigns each Stemp the first available colour at or above k. -/
def assignStempsTraversalGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      adjLists := CakeNodeMap.ofNatInfoMap 4 [(0, [2])]
      nodeTag := CakeNodeMap.ofNatInfoMap 4
        [(0, .sTemp), (1, .sTemp), (2, .fixed 2)] }
  let out := cakeAssignStemps 2 (fun _ _ _ => none) state
  out.nodeTag.get 0 == some (.fixed 3) &&
    out.nodeTag.get 1 == some (.fixed 2) &&
    out.nodeTag.get 2 == some (.fixed 2)

#guard assignStempsTraversalGuard

/- Cake's `insert_edge` reads both endpoint adjacency lists before writing,
   inserts both directions, and keeps each list descending without duplicates. -/
def insertEdgeGuard : Bool :=
  let adj : CakeNodeMap (List Nat) := CakeNodeMap.ofSize 4
  let one := cakeInsertEdge 1 3 adj
  let two := cakeInsertEdge 1 2 one
  let three := cakeInsertEdge 1 3 two
  one.get 1 == some [3] &&
    one.get 3 == some [1] &&
    two.get 1 == some [3, 2] &&
    two.get 2 == some [1] &&
    three.get 1 == some [3, 2] &&
    three.get 3 == some [1]

#guard insertEdgeGuard

/- Cake's list_insert_edge/clique_insert_edge inserts the tail first and
   connects every clique pair exactly once. -/
def cliqueInsertEdgeGuard : Bool :=
  let listEdges := cakeListInsertEdge 0 [1, 3] (CakeNodeMap.ofSize 4)
  let clique := cakeCliqueInsertEdge [0, 1, 2] (CakeNodeMap.ofSize 4)
  listEdges.get 0 == some [3, 1] &&
    listEdges.get 1 == some [0] &&
    listEdges.get 3 == some [0] &&
    clique.get 0 == some [2, 1] &&
    clique.get 1 == some [2, 0] &&
    clique.get 2 == some [1, 0]

#guard cliqueInsertEdgeGuard

/- Cake's `dec_degree` decrements exactly the neighbours of a node, saturates
   at zero, and leaves the source and non-neighbour degrees unchanged. -/
def decDegreeNeighboursGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      adjLists := CakeNodeMap.ofNatInfoMap 4 [(0, [1, 2])]
      degrees := CakeNodeMap.ofNatInfoMap 4
        [(0, 4), (1, 3), (2, 0), (3, 7)] }
  let out := cakeDecDegree 0 state
  out.degrees.get 0 == some 4 &&
    out.degrees.get 1 == some 2 &&
    out.degrees.get 2 == some 0 &&
    out.degrees.get 3 == some 7

#guard decDegreeNeighboursGuard

/-! The paired direct HOL `dec_deg` observations are in
    `scripts/hol-probes/reg_alloc_dec_deg_probe.out`: an in-range degree
    succeeds with `LUPDATE`, while an index at the list length returns
    `M_failure Subscript`. A missing option inside the dense array is a Lean
    representation hole, distinct from the HOL list-boundary case. -/
def decDegBoundaryGuard : Bool :=
  let represented : CakeRaState :=
    { CakeRaState.empty 1 with degrees := CakeNodeMap.ofList [3] }
  let monadicDecrement := cakeDecDegMonadic 0 represented
  let monadicOutside := cakeDecDegMonadic 1 represented
  let decremented := cakeDecDegStep 0 represented
  let outside := cakeDecDegStep 1 represented
  let sparse : CakeRaState :=
    { represented with degrees := { slots := #[none], outside := [] } }
  let hole := cakeDecDegStep 0 sparse
  let latched := cakeDecDeg 1 represented
  (match monadicDecrement with
    | .success () state => state.degrees.get 0 == some 2 && state.failure.isNone
    | _ => false) &&
  (match monadicOutside with
    | .failure .subscript state => state.degrees.get 0 == some 3
    | _ => false) &&
  (match decremented with
    | .ok state => state.degrees.get 0 == some 2 && state.failure.isNone
    | .error _ => false) &&
  (match outside with
    | .error .subscript => true
    | _ => false) &&
  (match hole with
    | .error .missingDegreeSlot => true
    | _ => false) &&
  (latched.failure == some .subscript) &&
  (latched.degrees.slots.size == represented.degrees.slots.size) &&
  (latched.degrees.outside == [])

#guard decDegBoundaryGuard

/-- Under the actual dense-array/list relation, the successful production step
    is HOL's in-range `LUPDATE` decrement. This keeps the paired oracle fixture
    from treating a caller-supplied representation assertion as evidence by
    itself: `hrep` is constructed with `ofList_representsHOLNodeList`, and the
    update relation is proved by `set_representsHOLNodeList`. -/
theorem cakeDecDegStep_matchesHolLupdate (state : CakeRaState)
    (m : CakeNodeMap Nat) (values : List Nat) (i : Nat)
    (hstate : state.degrees = m)
    (hrep : CakeNodeMap.RepresentsHOLNodeList m values)
    (hi : i < values.length) :
    cakeDecDegStep i state =
        .ok { state with degrees := CakeNodeMap.set m i (values[i] - 1) } ∧
      CakeNodeMap.RepresentsHOLNodeList
        (CakeNodeMap.set m i (values[i] - 1))
        (values.set i (values[i] - 1)) := by
  rcases hrep with ⟨houtside, hsize, hget⟩
  have hi' : i < m.slots.size := by simpa [hsize] using hi
  have hlookup : m.get i = some values[i] := by
    simpa using hget i hi
  have hslot : m.slots[i]? = some (some values[i]) := by
    simpa [CakeNodeMap.get, hi', houtside] using hlookup
  constructor
  · unfold cakeDecDegStep
    unfold cakeDecDegMonadic
    rw [hstate]
    simp only [ite_eq_left hi']
    rw [hslot]
  · exact CakeNodeMap.set_representsHOLNodeList m values
      ⟨houtside, hsize, hget⟩ i (values[i] - 1) hi

/-- The executable core exposes a result/state pair: under the checked array
    representation, successful `dec_deg` returns unit and the LUPDATE state. -/
theorem cakeDecDegMonadic_matchesHolLupdate (state : CakeRaState)
    (m : CakeNodeMap Nat) (values : List Nat) (i : Nat)
    (hstate : state.degrees = m)
    (hrep : CakeNodeMap.RepresentsHOLNodeList m values)
    (hi : i < values.length) :
    cakeDecDegMonadic i state =
        .success () { state with degrees := CakeNodeMap.set m i (values[i] - 1) } ∧
      CakeNodeMap.RepresentsHOLNodeList
        (CakeNodeMap.set m i (values[i] - 1))
        (values.set i (values[i] - 1)) := by
  rcases hrep with ⟨houtside, hsize, hget⟩
  have hi' : i < m.slots.size := by simpa [hsize] using hi
  have hlookup : m.get i = some values[i] := by
    simpa using hget i hi
  have hslot : m.slots[i]? = some (some values[i]) := by
    simpa [CakeNodeMap.get, hi', houtside] using hlookup
  constructor
  · unfold cakeDecDegMonadic
    rw [hstate]
    simp only [ite_eq_left hi']
    rw [hslot]
  · exact CakeNodeMap.set_representsHOLNodeList m values
      ⟨houtside, hsize, hget⟩ i (values[i] - 1) hi

example :
    CakeNodeMap.RepresentsHOLNodeList
      (CakeNodeMap.ofList [3]) [3] := by
  exact CakeNodeMap.ofList_representsHOLNodeList [3]

example :
    cakeDecDegStep 0 { CakeRaState.empty 1 with
        degrees := CakeNodeMap.ofList [3] } =
      .ok { CakeRaState.empty 1 with
        degrees := CakeNodeMap.set (CakeNodeMap.ofList [3]) 0 2 } := by
  have h := cakeDecDegStep_matchesHolLupdate
    (state := { CakeRaState.empty 1 with degrees := CakeNodeMap.ofList [3] })
    (m := CakeNodeMap.ofList [3]) (values := [3]) (i := 0) rfl
    (CakeNodeMap.ofList_representsHOLNodeList [3]) (by decide)
  simpa using h.1

example :
    cakeDecDegMonadic 1 { CakeRaState.empty 1 with
        degrees := CakeNodeMap.ofList [3] } =
      .failure .subscript { CakeRaState.empty 1 with
        degrees := CakeNodeMap.ofList [3] } := by
  apply cakeDecDegMonadic_subscript
  change (CakeNodeMap.ofList [3]).slots.size ≤ 1
  simp [CakeNodeMap.ofList]

def decDegFailureReachesAllocatorGuard : Bool :=
  let bijection : CakeNodeBijection :=
    { toAllocator := [], fromAllocator := [], nextNode := 0 }
  let invalid := cakeDecDeg 0 (CakeRaState.empty 0)
  cakeDoRegAllocFromState .simple none 1 [] bijection invalid == none

#guard decDegFailureReachesAllocatorGuard

/- Cake's `push_stack` zeroes the pushed node degree, clears its move-related
   flag, and prepends it to the stack while preserving unrelated state. -/
def pushStackGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      degrees := CakeNodeMap.ofNatInfoMap 4 [(1, 3), (2, 5)]
      moveRelated := CakeNodeMap.ofNatInfoMap 4 [(1, true), (2, false)]
      stack := [2] }
  let out := cakePushStack 1 state
  out.degrees.get 1 == some 0 &&
    out.degrees.get 2 == some 5 &&
    out.moveRelated.get 1 == some false &&
    out.moveRelated.get 2 == some false &&
    out.stack == [1, 2]

#guard pushStackGuard

/- Cake's worklist adders prepend their input lists without changing other
   state, matching the array-state updates in reg_allocScript.sml. -/
def worklistPrependGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      simpWl := [5]
      spillWl := [6]
      freezeWl := [7]
      unavailMovesWl := [(9, (1, 2))] }
  let simp := cakeAddSimpWl [1, 2] state
  let spill := cakeAddSpillWl [3, 4] state
  let freeze := cakeAddFreezeWl [8, 9] state
  let unavailable := cakeAddUnavailMovesWl [(10, (3, 4))] state
  simp.simpWl == [1, 2, 5] &&
    spill.spillWl == [3, 4, 6] &&
    freeze.freezeWl == [8, 9, 7] &&
    unavailable.unavailMovesWl == [(10, (3, 4)), (9, (1, 2))]

#guard worklistPrependGuard

/- Cake's `extend_clique` skips members already live, prepends newly discovered
   members to the live list, and links them to the existing clique. -/
def extendCliqueGuard : Bool :=
  let base := cakeCliqueInsertEdge [1, 2] (CakeNodeMap.ofSize 5)
  let (out, live) := cakeExtendClique [2, 3] [1, 2] base
  live == [3, 1, 2] &&
    out.get 1 == some [3, 2] &&
    out.get 2 == some [3, 1] &&
    out.get 3 == some [2, 1]

#guard extendCliqueGuard

/- Cake's split_degree selects low-degree uncoalesced allocation nodes,
   rejects high-degree/coalesced nodes, and keeps out-of-dimension nodes on
   the worklist side. -/
def splitDegreeGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      degrees := CakeNodeMap.ofNatInfoMap 4 [(0, 1), (1, 3), (2, 0)]
      coalesced := CakeNodeMap.ofNatInfoMap 4 [(2, 1)] }
  cakeSplitDegree state 4 2 0 &&
    !cakeSplitDegree state 4 2 1 &&
    !cakeSplitDegree state 4 2 2 &&
    cakeSplitDegree state 4 2 4

#guard splitDegreeGuard

/- Cake's `smerge` merges descending priority lists and takes the left head
   on equal priorities, preserving the tail order used by revive_moves. -/
def smergePriorityGuard : Bool :=
  cakeSMerge
      [(7, (1, 2)), (5, (3, 4))]
      [(7, (5, 6)), (6, (7, 8))] ==
    [(7, (1, 2)), (7, (5, 6)), (6, (7, 8)), (5, (3, 4))] &&
  cakeSMerge [] [(4, (9, 10))] == [(4, (9, 10))]

#guard smergePriorityGuard

/-! ## IRC graph construction guards

Structural checks for `cakeMkGraph` / `cakeExtendGraph` / `cakeMkTags` /
`cakeInitRaState`, derived from `reg_allocScript.sml`
(`sorted_insert`:184, `insert_edge`:201, `extend_clique`:235, `mk_graph`:1179,
`mk_tags`:1159).  The original threads its state through a monad over arrays,
so there is no standalone HOL oracle for the internal adjacency; the
end-to-end colouring oracle (`reg_alloc_probe.out`) validates the whole
machine once the worklist slices land. -/

private def graphAdj (tree : Flapjack.WordClashTree) (node : Nat) : List Nat :=
  let bij := Flapjack.RiscV.CakeRegAlloc.cakeMkBij tree
  let ta := Flapjack.RiscV.CakeAlloc.spDefault bij.toAllocator
  let (adj, _) := Flapjack.RiscV.CakeRegAlloc.cakeMkGraph ta tree [] {}
  Flapjack.RiscV.CakeRegAlloc.cakeAdjSub adj node

/-- Disjoint write and read sets never clash: no edges at all. -/
def graphDeltaDisjointGuard : Bool :=
  graphAdj (.delta [1] [3]) 0 == [] && graphAdj (.delta [1] [3]) 1 == []

/-- A write clique gets one edge per pair, adjacency sorted descending. -/
def graphDeltaCliqueGuard : Bool :=
  graphAdj (.delta [1, 3] []) 0 == [1] && graphAdj (.delta [1, 3] []) 1 == [0]

/-- The fixed `Set` node is a clique over the sorted members. -/
def graphSetCliqueGuard : Bool :=
  graphAdj (.set [4, 3]) 0 == [1] && graphAdj (.set [4, 3]) 1 == [0]

/-- Forced edges are added through the same bijection (vars 1 and 3
    are bijection members here: nodes 1 and 0). -/
def graphForcedEdgeGuard : Bool :=
  let bij := Flapjack.RiscV.CakeRegAlloc.cakeMkBij (.delta [1] [3])
  let ta := Flapjack.RiscV.CakeAlloc.spDefault bij.toAllocator
  let adj := Flapjack.RiscV.CakeRegAlloc.cakeExtendGraph ta [(1, 3)] {}
  Flapjack.RiscV.CakeRegAlloc.cakeAdjSub adj 0 == [1] &&
    Flapjack.RiscV.CakeRegAlloc.cakeAdjSub adj 1 == [0]

/-- Tagging: allocatable variable 9 -> Atemp, stack-only 13 -> Stemp,
physical 2 -> Fixed 1. -/
def graphTagsGuard : Bool :=
  let tags := Flapjack.RiscV.CakeRegAlloc.cakeMkTags 3 [(0, 9), (1, 13), (2, 2)]
    [13]
  tags.get 0 ==
      some Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.aTemp &&
    tags.get 1 ==
      some Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.sTemp &&
    tags.get 2 ==
      some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 1)

/-- `init_ra_state` combines the pieces: clique edge plus tags plus dim. -/
def graphInitGuard : Bool :=
  let state := Flapjack.RiscV.CakeRegAlloc.cakeInitRaState (.delta [1, 3] []) [] []
  Flapjack.RiscV.CakeRegAlloc.cakeAdjSub state.adjLists 0 == [1] &&
    Flapjack.RiscV.CakeRegAlloc.cakeAdjSub state.adjLists 1 == [0] &&
    state.nodeTag.get 0 ==
      some Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.aTemp &&
    state.nodeTag.get 1 ==
      some Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.sTemp &&
    state.dim == 2

/-- `init_alloc1_heu` on a two-node clique: the allocation temp sees the
    stack temp as unconsidered, so degree 0 lands on the simplify
    worklist and the stack temp stays out of `allocs`. -/
def heuDeltaGuard : Bool :=
  let state := Flapjack.RiscV.CakeRegAlloc.cakeInitRaState (.delta [1, 3] []) [] []
  let (count, after) := Flapjack.RiscV.CakeRegAlloc.cakeInitAlloc1Heu [] 4 state
  count == 1 &&
    after.degrees.get 0 == some 0 &&
    after.degrees.get 1 == some 1 &&
    after.coalesced.get 0 == some 0 &&
    after.coalesced.get 1 == some 1 &&
    after.simpWl == [0] && after.freezeWl == [] && after.spillWl == []

/-- `init_alloc1_heu` sorts the move worklist by descending priority and
    marks the non-fixed move endpoints move-related, sending the low-degree
    allocation temp to the freeze worklist instead of simplify. -/
def heuMovesGuard : Bool :=
  let state := Flapjack.RiscV.CakeRegAlloc.cakeInitRaState (.delta [1, 3] []) [] []
  let moves := [(1, (0, 1)), (3, (0, 1))]
  let (_, after) := Flapjack.RiscV.CakeRegAlloc.cakeInitAlloc1Heu moves 4 state
  after.availMovesWl == [(3, (0, 1)), (1, (0, 1))] &&
    after.moveRelated.get 0 == some true &&
    after.moveRelated.get 1 == some true &&
    after.freezeWl == [0] && after.simpWl == [] && after.spillWl == []

/-- `init_alloc1_heu` sends a clique of five allocation temps (degree 4)
    over the register threshold `k = 4` to the spill worklist. -/
def heuSpillGuard : Bool :=
  let state :=
    Flapjack.RiscV.CakeRegAlloc.cakeInitRaState
      (.delta [1, 5, 9, 13, 17] []) [] []
  let (count, after) := Flapjack.RiscV.CakeRegAlloc.cakeInitAlloc1Heu [] 4 state
  count == 5 && after.spillWl.length == 5 && after.simpWl == [] &&
    after.freezeWl == []

/-- A low physical register node counts towards its neighbour's degree
    (`considered_var`) but never enters the allocation worklist itself. -/
def heuFixedDegreeGuard : Bool :=
  let state := Flapjack.RiscV.CakeRegAlloc.cakeInitRaState (.delta [1, 2] [2, 1]) [] []
  let (count, after) := Flapjack.RiscV.CakeRegAlloc.cakeInitAlloc1Heu [] 4 state
  count == 1 &&
    after.degrees.get 1 == some 1 &&
    after.simpWl == [1] && after.spillWl == []

/-- Missing node tags use Cake's `sp_default`-style Atemp default in
    `considered_var`; stack temporaries remain unconsidered. -/
def consideredVarTagGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 2 with
      nodeTag := CakeNodeMap.ofNatInfoMap 2 [(0, .sTemp), (1, .fixed 2)] }
  !cakeConsideredVar state 4 0 &&
    cakeConsideredVar state 4 1 &&
    cakeConsideredVar state 4 7

#guard consideredVarTagGuard

/-- Normalise a colouring to the ascending original-variable order that the
    original sptree iteration produces. -/
def sortColouring (colours : Flapjack.NatInfoMap Nat) :
    List (Nat × Nat) :=
  colours.mergeSort (fun a b => a.1 < b.1)

/-- `sorting$PARTITION` reverses both buckets (`PART P l [] []` prepends). -/
def partOrderGuard : Bool :=
  partitionReversed (fun x => x % 2 == 0) [0, 1, 2] == ([2, 0], [1])

/-- `revive_moves` uses reversing HOL `PARTITION`; `sort_moves` then applies
    Cake's equal-priority order to the reversed revived bucket. -/
def reviveOrderGuard : Bool :=
  let base : Flapjack.RiscV.CakeRegAlloc.CakeRaState :=
    { Flapjack.RiscV.CakeRegAlloc.CakeRaState.empty 4 with
      adjLists := Flapjack.RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap 4 [(9, [5])],
      unavailMovesWl := [(1, (5, 9)), (1, (13, 5)), (1, (13, 17))],
      availMovesWl := [(2, (1, 1))] }
  let out := Flapjack.RiscV.CakeRegAlloc.cakeReviveMoves [9] base
  out.availMovesWl == [(2, (1, 1)), (1, (5, 9)), (1, (13, 5))] &&
    out.unavailMovesWl == [(1, (13, 17))]

def movesToSpOrderGuard : Bool :=
  let table := Flapjack.RiscV.CakeRegAlloc.cakeMovesToSp
    [(1, (2, 5)), (2, (2, 7)), (3, (2, 11))]
      (Flapjack.RiscV.CakeRegAlloc.CakeNodeMap.ofSize 12)
  table.get 2 ==
      some [(3, 11), (2, 7), (1, 5)] &&
    table.get 5 == some [(1, 2)]

/-- Cake's composed `moves_to_sp`/`resort_moves` output keeps the partner
    names in descending priority order before biased IRC preferences consume
    them.  The expected order is recorded by `reg_alloc_probe.out`, which
    evaluates the original Cake definitions directly. -/
def resortMovesSpOrderGuard : Bool :=
  let table := Flapjack.RiscV.CakeRegAlloc.cakeMovesToSp
    [(1, (2, 5)), (2, (2, 7)), (3, (2, 11))]
      (Flapjack.RiscV.CakeRegAlloc.CakeNodeMap.ofSize 12)
  let resorted := Flapjack.RiscV.CakeRegAlloc.cakeResortMovesSp table
  resorted.get 2 == some [11, 7, 5] &&
    resorted.get 5 == some [2] && resorted.get 7 == some [2] &&
    resorted.get 11 == some [2]

#guard reviveOrderGuard
#guard resortMovesSpOrderGuard

/-- `bg_ok` uses reversing HOL `PARTITION`, then `st_ex_FILTER`s each case list. -/
def bgOkOrderGuard : Bool :=
  let base : Flapjack.RiscV.CakeRegAlloc.CakeRaState :=
    { Flapjack.RiscV.CakeRegAlloc.CakeRaState.empty 4 with
      adjLists := Flapjack.RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap 4
        [(0, [1]), (1, [3, 0]), (2, [3]), (3, [2, 1, 0])],
      nodeTag := Flapjack.RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap 4
        ((List.range 4).map (fun i => (i, .aTemp))) }
  Flapjack.RiscV.CakeRegAlloc.cakeBgOk 3 0 3 base == some ([1], [2, 0])

def revivePartitionGuard : Bool :=
  let base : Flapjack.RiscV.CakeRegAlloc.CakeRaState :=
    { Flapjack.RiscV.CakeRegAlloc.CakeRaState.empty 4 with
      adjLists := Flapjack.RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap 4
        [(9, [17, 13, 5])],
      unavailMovesWl := [(1, (5, 9)), (1, (13, 5)), (1, (13, 17))] }
  let out := Flapjack.RiscV.CakeRegAlloc.cakeReviveMoves [9] base
  out.availMovesWl == [(1, (5, 9)), (1, (13, 5)), (1, (13, 17))] &&
    out.unavailMovesWl == []

/-- `reg_alloc` on a single write/read pair colours the write with the
    first free register and the unconnected stack temp with `k`. -/
def raDeltaPairGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.delta [1] [3]) [] []).map sortColouring ==
    some (sortColouring [(1, 0), (3, 4)])

/-- The threaded allocator entrypoint is definitionally the same computation as
    the compatibility wrapper, while allowing production callers to reuse the
    bijection and initial graph state they already built. -/
def threadedAllocatorEntryGuard : Bool :=
  let tree : WordClashTree := .delta [1] [3]
  let bij := cakeMkBij tree
  let state := cakeInitRaStateFromBij bij tree [] []
  cakeDoRegAlloc .irc none 4 [] tree [] [] ==
    cakeDoRegAllocFromState .irc none 4 [] bij state

#guard threadedAllocatorEntryGuard

/-- A physical-register read keeps its own register colour (`2 ↦ 1`). -/
def raDeltaFreeGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.delta [1] [2]) [] []).map sortColouring ==
    some (sortColouring [(1, 0), (2, 1)])

/-- A triangle `1-3-5` needs the spill channel for one participant. -/
def raDeltaTriangleGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.seq (.delta [1] [3])
         (.seq (.delta [3] [5]) (.delta [5] [1]))) [] []).map sortColouring ==
    some (sortColouring [(1, 0), (3, 4), (5, 1)])

/-- A stack-only variable is forced to the spill channel (`k` or above). -/
def raStackOnlyGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.delta [7] [1, 3]) [] [7]).map sortColouring ==
    some (sortColouring [(1, 0), (3, 4), (7, 4)])

/-- A move between `1` and `5` coalesces both to the register colour of
    `1` (`{1 ↦ 0; 5 ↦ 0}`). -/
def raMovesCoalesceGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 [(1, (1, 5))]
      (.delta [1] [5, 3]) [] []).map sortColouring ==
    some (sortColouring [(1, 0), (3, 4), (5, 0)])

/- Cake's `Simple` algorithm deliberately passes an empty move list to
   `init_alloc1_heu`; this direct row mirrors `ra_simple_moves` in
   `scripts/hol-probes/reg_alloc_probe.out` and keeps that algorithm branch
   distinct from the IRC/coalescing path above. -/
def raSimpleMovesGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .simple none 4 [(1, (1, 5))]
      (.delta [1] [5, 3]) [] []).map sortColouring ==
    some (sortColouring [(1, 0), (3, 4), (5, 0)])

#guard raSimpleMovesGuard

/- The fixed physical endpoint follows Cake's `do_coalesce_real` branch:
   x=2 is fixed, so coalescing y=5 into it does not increment x's degree.
   The expected colouring is the direct `reg_alloc_probe.out` oracle
   `ra_fixed_coalesce`. -/
def raFixedCoalesceGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4
      [(1, (2, 5))] (.delta [2] [5, 3]) [] []).map sortColouring ==
    some (sortColouring [(2, 1), (3, 4), (5, 1)])

#guard raFixedCoalesceGuard

/-- A self move is filtered out by the consistency check; the colouring
    then matches the coalesced case. -/
def raMovesSelfFilteredGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 [(1, (1, 1))]
      (.delta [1] [5, 3]) [] []).map sortColouring ==
    some (sortColouring [(1, 0), (3, 4), (5, 0)])

/-- A forced edge `1-5` separates the two nodes onto different registers
    (`{1 ↦ 1; 5 ↦ 0}`). -/
def raForcedEdgeGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.delta [1] [5, 3]) [(1, 5)] []).map sortColouring ==
    some (sortColouring [(1, 1), (3, 4), (5, 0)])

/- These two outputs are direct `reg_alloc_probe.out` observations.  A
   sequential pair has no interference and may share colour zero, while a
   same-delta clique must receive distinct colours. -/
def raOrderSeqGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.seq (.delta [9] []) (.delta [13] [])) [] []).map sortColouring ==
    some (sortColouring [(9, 0), (13, 0)])

def raOrderCliqueGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.delta [9, 13] []) [] []).map sortColouring ==
    some (sortColouring [(9, 0), (13, 1)])
/- Cake's `do_spill` (`reg_allocScript.sml:810-830`) chooses the first
   equal-degree candidate, pushes it, and unspills the remaining low-degree
   nodes onto the simplify worklist in Cake's reversed partition order. -/
def doSpillEqualDegreeGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 3 with
      degrees := CakeNodeMap.ofNatInfoMap 3 [(0, 0), (1, 0), (2, 0)]
      spillWl := [0, 1, 2] }
  let (changed, out) := cakeDoSpill none 1 state
  changed && out.stack == [0] && out.spillWl == [] &&
    out.simpWl == [2, 1] && out.freezeWl == [] &&
    (out.degrees.get 0).getD 0 == 0

#guard doSpillEqualDegreeGuard

/- Cake's `do_spill` returns `F` without touching the allocator state when
   the spill worklist is empty (`reg_allocScript.sml:809-830`).  Keep this
   boundary explicit so a driver cannot manufacture a stack entry or clear
   unrelated worklists on an empty candidate set. -/
def doSpillEmptyGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      simpWl := [1],
      spillWl := [],
      freezeWl := [2],
      availMovesWl := [(3, (1, 2))],
      unavailMovesWl := [(4, (2, 3))] }
  let (changed, out) := cakeDoSpill none 4 state
  !changed && out.dim == 4 && out.simpWl == [1] && out.spillWl == [] &&
    out.freezeWl == [2] && out.availMovesWl == [(3, (1, 2))] &&
    out.unavailMovesWl == [(4, (2, 3))] && out.stack == []

#guard doSpillEmptyGuard

/- Cake's `do_step` (`reg_allocScript.sml:832-857`) tries simplify before
   coalescing. With both worklists populated, simplify wins and leaves the
   available move untouched. -/
def doStepSimplifyPriorityGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 3 with
      simpWl := [1]
      moveRelated := CakeNodeMap.ofNatInfoMap 3 [(1, true), (2, true)]
      availMovesWl := [(1, (1, 2))] }
  let (changed, out) := cakeDoStep none 3 state
  changed && out.stack == [1] && out.simpWl == [] &&
    out.availMovesWl == [(1, (1, 2))] &&
    (out.coalesced.get 2).getD 2 == 2

#guard doStepSimplifyPriorityGuard

/- Cake's `do_step` reaches coalescing after an empty simplify worklist and
   before pre-freeze/freeze/spill.  Keep the driver-level priority distinct
   from the direct `do_coalesce` transition guard below. -/
def doStepCoalescePriorityGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 3 with
      moveRelated := CakeNodeMap.ofNatInfoMap 3 [(1, true), (2, true)]
      availMovesWl := [(1, (1, 2))] }
  let (changed, out) := cakeDoStep none 3 state
  changed && out.availMovesWl == [] && out.unavailMovesWl == [] &&
    (out.coalesced.get 2).getD 2 == 1 && out.stack == [2]

#guard doStepCoalescePriorityGuard

/- With no simplify/coalesce progress and an un-related freeze node, Cake's
   driver takes the pre-freeze branch; the pre-freeze pass immediately
   simplifies that node and leaves the allocator worklists empty. -/
def doStepPrefreezePriorityGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 3 with
      freezeWl := [1] }
  let (changed, out) := cakeDoStep none 3 state
  changed && out.stack == [1] && out.simpWl == [] &&
    out.freezeWl == [] && out.spillWl == []

#guard doStepPrefreezePriorityGuard

/- A move-related freeze node survives pre-freeze, so Cake's driver reaches
   `do_freeze` only after simplify/coalesce/pre-freeze report no progress. -/
def doStepFreezePriorityGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 3 with
      freezeWl := [1]
      moveRelated := CakeNodeMap.ofNatInfoMap 3 [(1, true), (2, true)]
      unavailMovesWl := [(1, (1, 2))] }
  let (changed, out) := cakeDoStep none 3 state
  changed && out.stack == [1] && out.simpWl == [] &&
    out.freezeWl == [] && out.spillWl == [] &&
    out.unavailMovesWl == [(1, (1, 2))]

#guard doStepFreezePriorityGuard

/- Cake's `do_step` reaches `do_spill` only after simplify, coalesce,
   pre-freeze, and freeze all report no progress.  With no cost table,
   `do_spill` selects the highest-degree candidate, preserving the residual
   spill worklist.  This covers the final priority branch from
   `reg_allocScript.sml:809-857`. -/
def doStepSpillFallbackGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 3 with
      degrees := CakeNodeMap.ofNatInfoMap 3 [(1, 1), (2, 3)]
      spillWl := [1, 2] }
  let (changed, out) := cakeDoStep none 1 state
  changed && out.stack == [2] && out.spillWl == [1] &&
    out.simpWl == [] && out.freezeWl == []

#guard doStepSpillFallbackGuard

/- Cake's `rpt_do_step` (`reg_allocScript.sml:860-868`) stops early when the
   next `do_step` makes no progress.  A one-node spill performs exactly one
   transition and then terminates before consuming the remaining fuel. -/
def rptDoStepEarlyStopGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 2 with
      degrees := CakeNodeMap.ofNatInfoMap 2 [(1, 1)]
      spillWl := [1] }
  let out := cakeRptDoStep none 1 3 state
  out.stack == [1] && out.spillWl == [] && out.simpWl == [] &&
    out.freezeWl == []

#guard rptDoStepEarlyStopGuard

/- Cake's `unspill` (`reg_allocScript.sml:378-391`) partitions the spill
   worklist with the HOL reversed-accumulator order, sending newly low-degree,
   non-move-related nodes to `simpWl`. -/
def unspillTransitionGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 5 with
      degrees := CakeNodeMap.ofNatInfoMap 5 [(1, 0), (2, 2), (3, 1)]
      spillWl := [1, 2, 3] }
  let out := cakeUnspill 2 state
  out.spillWl == [2] && out.simpWl == [1, 3] &&
    out.freezeWl == [] && out.stack == []

#guard unspillTransitionGuard

/- The canonical `reg_alloc_probe.out` cost-sensitive case exercises
   `do_spill` with a non-`NONE` source-keyed table and one allocatable colour:
   Cake selects the high-cost source 5 for colour 0, leaving 1 and 9 in the
   two spill colours. -/
def raSpillCostGuard : Bool :=
  let costs : Flapjack.NatInfoMap Nat := [(1, 1), (5, 100), (9, 1)]
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc
      (some (cakeSpillCostMap 3 costs)) 1 []
      (.delta [1, 5, 9] []) [] []).map sortColouring ==
    some (sortColouring [(1, 1), (5, 0), (9, 2)])

/- Cake's `st_ex_list_MIN_cost` scans the remaining spill worklist in order,
   replacing the selected node only on a strict lower cost.  This direct case
   checks both the cost division and the reversed residual list from
   `reg_allocScript.sml:773-790`. -/
def stExMinCostOrderGuard : Bool :=
  let degrees := CakeNodeMap.ofNatInfoMap 4 [(0, 2), (1, 1), (2, 2)]
  let costs := CakeNodeMap.ofNatInfoMap 4 [(0, 10), (1, 100), (2, 1)]
  cakeStExListMinCost degrees costs [1, 2] 4 0 5 [] == (2, [0, 1])

#guard stExMinCostOrderGuard

/- Equal spill costs retain the first candidate: Cake's `v > cost` test is
   strict, while each visited non-selected node is prepended to the residual
   worklist. -/
def stExMinCostTieGuard : Bool :=
  let degrees := CakeNodeMap.ofNatInfoMap 4 [(0, 2), (1, 2), (2, 2)]
  let costs := CakeNodeMap.ofNatInfoMap 4 [(0, 10), (1, 10), (2, 10)]
  cakeStExListMinCost degrees costs [1, 2] 4 0 5 [] == (0, [2, 1])

#guard stExMinCostTieGuard

/- Cake's `safe_div` maps a zero degree to cost zero before the strict
   comparison; this keeps the spill scan total without inventing a divisor. -/
def stExMinCostZeroDegreeGuard : Bool :=
  let degrees := CakeNodeMap.ofNatInfoMap 4 [(0, 2), (1, 0), (2, 2)]
  let costs := CakeNodeMap.ofNatInfoMap 4 [(0, 10), (1, 7), (2, 1)]
  cakeSafeDiv 7 0 == 0 &&
    cakeStExListMinCost degrees costs [1, 2] 4 0 1 [] == (1, [2, 0])

#guard stExMinCostZeroDegreeGuard

/- Cake's cost-free `do_spill` fallback uses `st_ex_list_MAX_deg`: it scans
   the remaining worklist, replacing the selected node only on a strict
   degree increase and retaining the reversed residual list. -/
def stExMaxDegOrderGuard : Bool :=
  let degrees := CakeNodeMap.ofNatInfoMap 4 [(0, 2), (1, 1), (2, 3)]
  cakeStExListMaxDeg degrees [1, 2] 4 0 2 [] == (2, [0, 1])

#guard stExMaxDegOrderGuard

/- Equal degrees retain the first spill candidate: Cake's comparison is
   strict, so a tie must not perturb the selected node. -/
def stExMaxDegTieGuard : Bool :=
  let degrees := CakeNodeMap.ofNatInfoMap 4 [(0, 2), (1, 2), (2, 2)]
  cakeStExListMaxDeg degrees [1, 2] 4 0 2 [] == (0, [2, 1])

#guard stExMaxDegTieGuard

/- End-to-end `do_spill` oracle: Cake selects node 2, pushes it, and
   `unspill` moves the residual low-degree node 1 to the simplify worklist. -/
def doSpillTransitionGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      degrees := CakeNodeMap.ofNatInfoMap 4 [(0, 2), (1, 1), (2, 3)],
      spillWl := [1, 2] }
  let (did, after) := cakeDoSpill none 4 state
  did && after.stack == [2] && after.simpWl == [1] &&
    after.freezeWl == [] && after.spillWl == []

#guard doSpillTransitionGuard

/- Cake's `dec_degree` skips an out-of-dimension node before reading its
   adjacency list.  This matters for the functional map's explicit `outside`
   bindings: an out-of-range edge must not decrement an in-range neighbour. -/
def decDegreeOutOfDimGuard : Bool :=
  let adj := cakeInsertEdge 3 1 (CakeNodeMap.ofSize 2)
  let state : CakeRaState :=
    { CakeRaState.empty 2 with
      adjLists := adj,
      degrees := CakeNodeMap.ofNatInfoMap 2 [(1, 2)] }
  let after := cakeDecDegree 3 state
  (after.degrees.get 1).getD 0 == 2

#guard decDegreeOutOfDimGuard

/- Cake's `respill` (`reg_allocScript.sml:659-674`) moves a freeze-worklist
   node back to the spill worklist only when its degree reaches `k`; it
   removes that node from `freezeWl` and prepends it to `spillWl`. -/
def respillWorklistGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      degrees := CakeNodeMap.ofNatInfoMap 4 [(3, 4)]
      spillWl := [1, 2]
      freezeWl := [3] }
  let moved := cakeRespill 4 3 state
  moved.spillWl == [3, 1, 2] && moved.freezeWl == [] &&
    (moved.degrees.get 3).getD 0 == 4

def respillBelowThresholdGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      degrees := CakeNodeMap.ofNatInfoMap 4 [(3, 3)]
      spillWl := [1]
      freezeWl := [3] }
  let unchanged := cakeRespill 4 3 state
  unchanged.spillWl == [1] && unchanged.freezeWl == [3]

#guard respillWorklistGuard
#guard respillBelowThresholdGuard

/- Cake's `do_prefreeze` (`reg_allocScript.sml:727-747`) filters the
   coalescing worklists, resets move-related flags, partitions freeze nodes,
   and immediately runs `do_simplify`.  With no related moves, both initial
   freeze nodes are simplified in reverse worklist order; the low-degree
   spill nodes are then reintroduced on the simplify worklist. -/
def prefreezeTransitionGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      freezeWl := [1, 2]
      spillWl := [3, 4] }
  let (changed, out) := cakeDoPrefreeze 4 state
  changed && out.stack == [2, 1] && out.simpWl == [4, 3] &&
    out.freezeWl == [] && out.spillWl == []

#guard prefreezeTransitionGuard

/- Cake's `do_simplify` (`reg_allocScript.sml:400-415`) processes the whole
   simplify worklist before pushing it, preserving the worklist order in the
   reverse stack order and then clearing `simpWl`. -/
def simplifyBatchGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      degrees := CakeNodeMap.ofNatInfoMap 4 [(1, 1), (2, 2)]
      simpWl := [1, 2] }
  let (changed, simplified) := cakeDoSimplify 3 state
  changed && simplified.simpWl == [] && simplified.stack == [2, 1] &&
    (simplified.degrees.get 1).getD 0 == 0 &&
    (simplified.degrees.get 2).getD 0 == 0

#guard simplifyBatchGuard
/- Cake's `dec_degree` (`reg_allocScript.sml:263-272`) is a safe no-op for
   an out-of-dimension node, even if an outside adjacency entry exists. -/
def decDegreeOutOfDimNoOpGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 3 with
      adjLists := CakeNodeMap.ofNatInfoMap 3 [(5, [1])]
      degrees := CakeNodeMap.ofNatInfoMap 3 [(1, 2)] }
  let out := cakeDecDegree 5 state
  (out.degrees.get 1).getD 0 == 2

#guard decDegreeOutOfDimNoOpGuard

/- Cake's `do_coalesce` (`reg_allocScript.sml:676-698`) consumes the first
   compatible move, coalesces its second endpoint into the first, clears the
   available-move worklist, and pushes the coalesced endpoint onto the stack. -/
def coalesceWorklistSuccessGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 3 with
      moveRelated := CakeNodeMap.ofNatInfoMap 3 [(1, true), (2, true)]
      availMovesWl := [(1, (1, 2))] }
  let (changed, out) := cakeDoCoalesce 3 state
  changed && out.availMovesWl == [] && out.unavailMovesWl == [] &&
    (out.coalesced.get 2).getD 2 == 1 && out.stack == [2] &&
    (out.moveRelated.get 2).getD true == false

#guard coalesceWorklistSuccessGuard

/- Cake's `st_ex_FIRST`/`do_coalesce` (`reg_allocScript.sml:636-698`)
   rejects a self-move through `consistency_ok`: it is not moved to the
   unavailable list, while the failed coalescing pass clears avail_moves_wl. -/
def coalesceSelfMoveRejectedGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 3 with
      moveRelated := CakeNodeMap.ofNatInfoMap 3 [(1, true)]
      availMovesWl := [(1, (1, 1))] }
  let (changed, out) := cakeDoCoalesce 3 state
  !changed && out.availMovesWl == [] && out.unavailMovesWl == []

#guard coalesceSelfMoveRejectedGuard

/-- Cake's coalesce_parent follows a non-fixed parent chain and compresses
   the starting node to the fixed ancestor (reg_allocScript.sml:589-612).
   This is distinct from the worklist coalesce guard above: it checks the
   recursive ancestor walk and its in-place parent update directly. -/
def coalesceParentCompressionGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 5 with
      nodeTag := CakeNodeMap.ofNatInfoMap 5 [(2, .fixed 1)]
      coalesced := CakeNodeMap.ofNatInfoMap 5 [(4, 3), (3, 2)] }
  let (root, out) := cakeCoalesceParent 4 state
  root == 2 && (out.coalesced.get 4).getD 4 == 2

#guard coalesceParentCompressionGuard

/- Cake's `do_freeze` (`reg_allocScript.sml:749-764`) decrements the frozen
   node's neighbours, pushes it, removes it from `freezeWl`, then unspills a
   spill node that has become low degree into the simplify worklist. -/
def freezeWorklistTransitionGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      adjLists := CakeNodeMap.ofNatInfoMap 4 [(1, [2]), (2, [1])]
      degrees := CakeNodeMap.ofNatInfoMap 4 [(1, 1), (2, 1)]
      moveRelated := CakeNodeMap.ofNatInfoMap 4 [(1, true), (2, false)]
      freezeWl := [1]
      spillWl := [2] }
  let (changed, out) := cakeDoFreeze 2 state
  changed && out.freezeWl == [] && out.spillWl == [] &&
    out.simpWl == [2] && out.stack == [1] &&
    (out.degrees.get 1).getD 0 == 0 &&
    (out.degrees.get 2).getD 0 == 0 &&
    (out.moveRelated.get 1).getD true == false

#guard freezeWorklistTransitionGuard
/-! These control-flow cases mirror the remaining `get_prefs_def` equations
    in Cake's `word_allocScript.sml`: both branch arms are traversed with the
    else-arm as the incoming accumulator, and a handled call traverses its
    handler after its return continuation. -/
/-- `sort_moves` flips equal-priority moves relative to the input order
    (probe `sort_moves_probe.out` `sm_ties_two`). -/
def qsortTiesTwoGuard : Bool :=
  Flapjack.RiscV.CakeRegAlloc.cakeSortMoves [(1, (13, 5)), (1, (5, 9))] ==
    [(1, (5, 9)), (1, (13, 5))]

/-- A second equal-priority flip case (probe `sm_ties_three`): the two
    priority-3 moves come out reversed. -/
def qsortTiesThreeGuard : Bool :=
  Flapjack.RiscV.CakeRegAlloc.cakeSortMoves
      [(3, (1, 2)), (1, (9, 9)), (3, (7, 8))] ==
    [(3, (7, 8)), (3, (1, 2)), (1, (9, 9))]

/-! The tail merge split changes equal-priority order at the first
    non-trivial recursion sizes; these are direct `reg_alloc$sort_moves`
    oracle cases for lengths four through six. -/
def sortMovesTailSplitGuard : Bool :=
  Flapjack.RiscV.CakeRegAlloc.cakeSortMoves
      [(7, (1, 2)), (7, (3, 4)), (7, (5, 6)), (7, (7, 8))] ==
      [(7, (7, 8)), (7, (5, 6)), (7, (3, 4)), (7, (1, 2))] &&
  Flapjack.RiscV.CakeRegAlloc.cakeSortMoves
      [(7, (1, 2)), (7, (3, 4)), (7, (5, 6)), (7, (7, 8)), (7, (9, 10))] ==
      [(7, (9, 10)), (7, (7, 8)), (7, (5, 6)), (7, (3, 4)), (7, (1, 2))] &&
  Flapjack.RiscV.CakeRegAlloc.cakeSortMoves
      [(7, (1, 2)), (7, (3, 4)), (7, (5, 6)), (7, (7, 8)), (7, (9, 10)),
       (7, (11, 12))] ==
      [(7, (11, 12)), (7, (9, 10)), (7, (7, 8)), (7, (5, 6)), (7, (3, 4)),
       (7, (1, 2))]

/-! Cake's pairwise merge sort reverses a long run of equal priorities. -/
def sortMovesLongTieGuard : Bool :=
  Flapjack.RiscV.CakeRegAlloc.cakeSortMoves
      [(12, (133, 173)), (12, (129, 133)), (12, (117, 149)),
       (12, (113, 117)), (12, (105, 121)), (12, (101, 157)),
       (12, (97, 101)), (12, (89, 105)), (12, (85, 141)),
       (12, (81, 85)), (12, (73, 89)), (12, (69, 165)),
       (12, (65, 69)), (12, (57, 73)), (12, (53, 137)),
       (12, (49, 53)), (12, (45, 57)), (12, (41, 45)),
       (12, (2, 185)), (22, (0, 37))] ==
      [(22, (0, 37)), (12, (2, 185)), (12, (41, 45)),
       (12, (45, 57)), (12, (49, 53)), (12, (53, 137)),
       (12, (57, 73)), (12, (65, 69)), (12, (69, 165)),
       (12, (73, 89)), (12, (81, 85)), (12, (85, 141)),
       (12, (89, 105)), (12, (97, 101)), (12, (101, 157)),
       (12, (105, 121)), (12, (113, 117)), (12, (117, 149)),
       (12, (129, 133)), (12, (133, 173))]

/-- Strictly descending priorities sort descending (probe `sm_desc`). -/
def qsortDescGuard : Bool :=
  Flapjack.RiscV.CakeRegAlloc.cakeSortMoves
      [(1, (13, 5)), (3, (5, 9)), (2, (7, 8))] ==
    [(3, (5, 9)), (2, (7, 8)), (1, (13, 5))]

/-- `assign_Stemp_tag` uses Cake's non-strict bad-colour ordering; equal
    colours therefore retain Cake's merge-sort tie order. -/
def stempBadColourTieGuard : Bool :=
  Flapjack.RiscV.CakeRegAlloc.cakeSort (fun a b => a <= b) [4, 4, 1, 4] ==
    [1, 4, 4, 4]

#guard stempBadColourTieGuard

/-- A move onto a stack temp keeps the stack temp above the register
    count while the two alloc vars coalesce (probe `ra_moves_stemp`). -/
def raMovesStempGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 [(1, (3, 9))]
      (.delta [9] [13, 3]) [] []).map sortColouring ==
    some (sortColouring [(3, 4), (9, 0), (13, 0)])

/-- The same shape with a higher move priority (probe
    `ra_moves_stemp_hi`). -/
def raMovesStempHiGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 [(5, (3, 9))]
      (.delta [9] [13, 3]) [] []).map sortColouring ==
    some (sortColouring [(3, 4), (9, 0), (13, 0)])

/-- `neg_first_match_col` projects each candidate through the node tag
    table: non-`Fixed` tags are skipped and a missing entry stops the
    search. -/
def negFirstMatchProjectionGuard : Bool :=
  let state : Flapjack.RiscV.CakeRegAlloc.CakeRaState :=
    { Flapjack.RiscV.CakeRegAlloc.CakeRaState.empty 7 with
      nodeTag := Flapjack.RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap 7
        [(4, .fixed 6), (5, .aTemp), (6, .fixed 2)] }
  Flapjack.RiscV.CakeRegAlloc.cakeNegFirstMatchCol state 3 [2] [4, 5, 6] ==
      some 6 &&
    Flapjack.RiscV.CakeRegAlloc.cakeNegFirstMatchCol state 3 [6] [6] ==
      none &&
    Flapjack.RiscV.CakeRegAlloc.cakeNegFirstMatchCol state 3 [] [5, 7] ==
      none

/- Cake's `biased_pref` first tries the coalesced root, then the move-partner
   table; `neg_biased_pref` scans only non-conflicting stack colours. These
   direct cases pin the preference inputs consumed by IRC. -/
def biasedPreferenceGuard : Bool :=
  let rootState : CakeRaState :=
    { CakeRaState.empty 4 with
      nodeTag := CakeNodeMap.ofNatInfoMap 4 [(2, .fixed 1)]
      coalesced := CakeNodeMap.ofNatInfoMap 4 [(1, 2)] }
  let partnerState : CakeRaState :=
    { CakeRaState.empty 4 with
      -- The root tag must exist for the original preference to reach its
      -- partner table; an absent root instead triggers handled Subscript.
      nodeTag := CakeNodeMap.ofNatInfoMap 4 [(1, .aTemp), (3, .fixed 0)] }
  let emptyMoves := CakeNodeMap.ofSize 4
  let partnerMoves := CakeNodeMap.ofNatInfoMap 4 [(1, [3])]
  cakeBiasedPref rootState emptyMoves 1 [0, 1] == some 1 &&
    cakeBiasedPref partnerState partnerMoves 1 [0, 1] == some 0 &&
    cakeBiasedPref partnerState partnerMoves 4 [0, 1] == none

def negBiasedPreferenceGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      nodeTag := CakeNodeMap.ofNatInfoMap 4
        [(2, .fixed 2), (3, .fixed 4)] }
  let moves := CakeNodeMap.ofNatInfoMap 4 [(1, [2, 3])]
  cakeNegBiasedPref state 2 moves 1 [2] == some 4 &&
    cakeNegBiasedPref state 2 moves 4 [2] == none

#guard biasedPreferenceGuard
#guard negBiasedPreferenceGuard

/- `full_consistency_ok` rejects out-of-dimension and clashing moves, permits
   Atemp/low-fixed endpoints, and rejects two low fixed endpoints. -/
def fullConsistencyGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      nodeTag := CakeNodeMap.ofNatInfoMap 4
        [(0, .aTemp), (1, .aTemp), (2, .fixed 1), (3, .fixed 3)]
      adjLists := CakeNodeMap.ofNatInfoMap 4 [(0, [2]), (2, [0])] }
  cakeFullConsistencyOk state 2 0 1 &&
    !cakeFullConsistencyOk state 2 0 2 &&
    !cakeFullConsistencyOk state 2 2 3 &&
    !cakeFullConsistencyOk state 2 0 4

#guard fullConsistencyGuard

/- `canonize_move` puts a fixed endpoint first; otherwise it orders allocator
   nodes ascending, matching reg_allocScript.sml:614-624. -/
def canonizeMoveGuard : Bool :=
  let fixedLeft : CakeRaState :=
    { CakeRaState.empty 4 with
      nodeTag := CakeNodeMap.ofNatInfoMap 4 [(2, .fixed 1), (3, .aTemp)] }
  let fixedRight : CakeRaState :=
    { CakeRaState.empty 4 with
      nodeTag := CakeNodeMap.ofNatInfoMap 4 [(2, .aTemp), (3, .fixed 2)] }
  let allAtemps : CakeRaState := CakeRaState.empty 6
  cakeCanonizeMove fixedLeft 2 3 == (2, 3) &&
    cakeCanonizeMove fixedRight 2 3 == (3, 2) &&
    cakeCanonizeMove allAtemps 5 2 == (2, 5)

#guard canonizeMoveGuard

/- Cake's `reset_move_related` (`reg_allocScript.sml:708-725`) first clears
   the whole dimension, then marks exactly the non-fixed endpoints of the
   surviving unavailable moves. -/
def resetMoveRelatedGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      nodeTag := CakeNodeMap.ofNatInfoMap 4 [(1, .fixed 2)]
      moveRelated := CakeNodeMap.ofNatInfoMap 4
        [(0, true), (1, true), (2, true), (3, true)] }
  let out := cakeResetMoveRelated [(1, (0, 1)), (2, (2, 3))] state
  (out.moveRelated.get 0).getD false == true &&
    (out.moveRelated.get 1).getD true == false &&
    (out.moveRelated.get 2).getD false == true &&
    (out.moveRelated.get 3).getD false == true

#guard resetMoveRelatedGuard

/- Cake's `remove_colours` (`reg_allocScript.sml:874-897`) removes every
   fixed-neighbour colour while leaving allocation and stack temporary tags
   untouched. -/
def removeColoursGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      nodeTag := CakeNodeMap.ofNatInfoMap 4
        [(1, .fixed 0), (2, .fixed 2), (3, .aTemp)] }
  cakeRemoveColours state [1, 3, 2] [0, 1, 2, 3] == [1, 3]

#guard removeColoursGuard

/- The HOL allocator updates fixed-size array cells.  Repeated writes to an
   existing node must therefore not retain an unbounded history in the Lean
   association-list representation. -/
def mapUpdateBoundedGuard : Bool :=
  let initial : Flapjack.NatInfoMap Nat := [(0, 0), (1, 1)]
  let updated := (List.range 100).foldl
    (fun map value => cakeMapUpdate map 0 value) initial
  let inserted := cakeMapUpdate updated 2 7
  updated.length == 2 &&
    cakeMapLookup updated 0 == some 99 &&
    cakeMapLookup updated 1 == some 1 &&
    inserted.length == 3 && cakeMapLookup inserted 2 == some 7

/-- `word_alloc` passes `get_heuristics` costs keyed by source variables
    directly to `reg_alloc`; the array adapter preserves those keys, including
    source names outside the dense allocator array. -/
def sourceSpillCostKeyGuard : Bool :=
  let costs : Flapjack.NatInfoMap Nat := [(1, 10), (2, 1), (5, 20)]
  let table := cakeSpillCostMap 3 costs
  table.get 1 == some 10 && table.get 2 == some 1 && table.get 5 == some 20 &&
    table.get 0 == none

/- Cake's fixed allocator array exposes source-keyed costs outside its dense
   dimension through the same lookup/update semantics as the HOL sptree.
   The first source binding also wins, matching lookup_any on the original map. -/
def sourceSpillCostRoundTripGuard : Bool :=
  let costs : Flapjack.NatInfoMap Nat := [(1, 10), (1, 11), (5, 20)]
  let table := cakeSpillCostMap 3 costs
  table.toNatInfoMap == [(1, 10), (5, 20)] &&
    table.get 5 == some 20

def sourceMovePhysicalFallbackGuard : Bool :=
  let index := Flapjack.RiscV.CakeRegAlloc.cakeAllocatorIndex []
  Flapjack.RiscV.CakeRegAlloc.cakeUpdateMove
      (Flapjack.RiscV.CakeRegAlloc.cakeAllocatorIndexLookup index)
      (7, (2, 9)) == (7, (0, 1))


/- Cake's mk_bij_aux enumerates a Set through the Patricia-tree toAList,
   whose order is not ascending.  This fixture is the checked HOL order
   [0, 4, 12, 6] and guards the allocator node numbering that feeds
   register-colour tie breaks. -/
def cakeBijSetPatriciaGuard : Bool :=
  let bij := cakeMkBij (.set [0, 4, 6, 12])
  lookupNatInfo 0 bij.toAllocator == some 0 &&
    lookupNatInfo 4 bij.toAllocator == some 1 &&
    lookupNatInfo 12 bij.toAllocator == some 2 &&
    lookupNatInfo 6 bij.toAllocator == some 3

#guard cakeBijSetPatriciaGuard
#guard sortMovesTailSplitGuard
#guard sortMovesLongTieGuard
#guard raDeltaTriangleGuard
#guard raForcedEdgeGuard

-- Native adjacency Subscript is preserved, rather than replaced by an empty row.
example : (cakeDecDegree 0 { CakeRaState.empty 1 with
    adjLists := CakeNodeMap.ofList ([] : List (List Nat)) }).failure =
      some .subscript := by
  simp [cakeDecDegree, CakeRaState.empty, CakeNodeMap.ofList,
    CakeNodeMap.get, cakeMapLookup, lookupNatInfo]

-- A previously latched error prevents every subsequent neighbour transition.
example (state : CakeRaState) (node : Nat) (error : CakeRaFailure)
    (failed : state.failure = some error) : cakeDecDegree node state = state := by
  simp [cakeDecDegree, failed]

end Flapjack.Test.CakeRegAlloc
