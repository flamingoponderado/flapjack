import Flapjack.Compiler.Backend.RegAlloc.Carriers
import Flapjack.RiscV.CakeRegAlloc

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc

/-- Constructor-for-constructor production tag translation. Flapjack carrier
infrastructure, with no separate HOL declaration. -/
def Tag.toProduction : Tag → CakeNodeTag
  | .Fixed colour => .fixed colour
  | .Atemp => .aTemp
  | .Stemp => .sTemp

/-- The optional production adjacency index must answer every membership query
exactly as its canonical adjacency lists, including absent slots. This is a
cache invariant, not a native graph or phase-success assumption. -/
def ProductionAdjacencyCacheSound (state : CakeRaState) : Prop :=
  match state.adjSets with
  | none => True
  | some cache => ∀ node neighbour,
      (cache.get node).map (fun neighbours => neighbours.contains neighbour) =
        (state.adjLists.get node).map (fun neighbours => decide (neighbour ∈ neighbours))

/-- Complete native/production allocator carrier relation. All twelve native
fields are represented, and both extra production fields are constrained.
The array translation is justified by checked bounded list witnesses. This
untagged infrastructure does not establish monadic transition equivalence. -/
structure ProductionStateRel (native : State) (production : CakeRaState) : Prop where
  adjacency : CakeNodeMap.RepresentsHOLNodeList production.adjLists native.adj_ls
  tags : CakeNodeMap.RepresentsHOLNodeList production.nodeTag (native.node_tag.map Tag.toProduction)
  degrees : CakeNodeMap.RepresentsHOLNodeList production.degrees native.degrees
  parents : CakeNodeMap.RepresentsHOLNodeList production.coalesced native.coalesced
  moveRelated : CakeNodeMap.RepresentsHOLNodeList production.moveRelated native.move_related
  dimension : production.dim = native.dim
  simplify : production.simpWl = native.simp_wl
  spill : production.spillWl = native.spill_wl
  freeze : production.freezeWl = native.freeze_wl
  availableMoves : production.availMovesWl = native.avail_moves_wl
  unavailableMoves : production.unavailMovesWl = native.unavail_moves_wl
  stack : production.stack = native.stack
  adjacencyCache : ProductionAdjacencyCacheSound production
  failure : production.failure = none

/-- Canonical complete embedding of a native allocator state. The optional
lookup cache is absent; no executable phase is rerun and no field is discarded.
Actual cached initializer correspondence is a separate prerequisite. -/
def State.toProduction (native : State) : CakeRaState :=
  { adjLists := CakeNodeMap.ofList native.adj_ls
    adjSets := none
    nodeTag := CakeNodeMap.ofList (native.node_tag.map Tag.toProduction)
    degrees := CakeNodeMap.ofList native.degrees
    coalesced := CakeNodeMap.ofList native.coalesced
    moveRelated := CakeNodeMap.ofList native.move_related
    dim := native.dim
    simpWl := native.simp_wl
    spillWl := native.spill_wl
    freezeWl := native.freeze_wl
    availMovesWl := native.avail_moves_wl
    unavailMovesWl := native.unavail_moves_wl
    stack := native.stack
    failure := none }

/-- Every native state has a complete production representation, without a
representation, well-formedness, or successful-phase premise. -/
theorem State.toProduction_rel (native : State) : ProductionStateRel native native.toProduction := by
  exact {
    adjacency := CakeNodeMap.ofList_representsHOLNodeList _
    tags := CakeNodeMap.ofList_representsHOLNodeList _
    degrees := CakeNodeMap.ofList_representsHOLNodeList _
    parents := CakeNodeMap.ofList_representsHOLNodeList _
    moveRelated := CakeNodeMap.ofList_representsHOLNodeList _
    dimension := rfl
    simplify := rfl
    spill := rfl
    freeze := rfl
    availableMoves := rfl
    unavailableMoves := rfl
    stack := rfl
    adjacencyCache := True.intro
    failure := rfl }

/-- Bounded degree reads agree with native list subscripts. -/
theorem ProductionStateRel.degree_read {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (node : Nat)
    (bound : node < native.degrees.length) :
    production.degrees.get node = some native.degrees[node] :=
  related.degrees.2.2 node bound

/-- Bounded adjacency reads preserve the entire ordered neighbour list. -/
theorem ProductionStateRel.adjacency_read {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (node : Nat)
    (bound : node < native.adj_ls.length) :
    production.adjLists.get node = some native.adj_ls[node] :=
  related.adjacency.2.2 node bound

/-- Bounded parent reads preserve the exact native parent name. -/
theorem ProductionStateRel.parent_read {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (node : Nat)
    (bound : node < native.coalesced.length) :
    production.coalesced.get node = some native.coalesced[node] :=
  related.parents.2.2 node bound

/-- Bounded move-related reads preserve the exact native Boolean. -/
theorem ProductionStateRel.moveRelated_read {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (node : Nat)
    (bound : node < native.move_related.length) :
    production.moveRelated.get node = some native.move_related[node] :=
  related.moveRelated.2.2 node bound

/-- Bounded tag reads commute with constructor-for-constructor translation. -/
theorem ProductionStateRel.tag_read {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (node : Nat)
    (bound : node < native.node_tag.length) :
    production.nodeTag.get node = some (native.node_tag[node].toProduction) := by
  have mapped := related.tags.2.2 node (by simpa using bound)
  simpa using mapped

/-- A bounded tag write preserves the complete relation. -/
theorem ProductionStateRel.tag_write {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (node : Nat) (value : Tag)
    (bound : node < native.node_tag.length) :
    ProductionStateRel {native with node_tag := native.node_tag.set node value}
      {production with nodeTag := production.nodeTag.set node value.toProduction} := by
  refine { related with tags := ?_ }
  simpa using CakeNodeMap.set_representsHOLNodeList _ _ related.tags node value.toProduction
    (by simpa using bound)

/-- A bounded adjacency write in an uncached state preserves the complete
relation. Cached graph updates require their separate membership invariant;
this lemma does not assume or claim that they are already established. -/
theorem ProductionStateRel.adjacency_write_uncached {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (node : Nat) (value : List Nat)
    (bound : node < native.adj_ls.length) (uncached : production.adjSets = none) :
    ProductionStateRel {native with adj_ls := native.adj_ls.set node value}
      {production with adjLists := production.adjLists.set node value} := by
  refine { related with
    adjacency := CakeNodeMap.set_representsHOLNodeList _ _ related.adjacency node value bound
    adjacencyCache := ?_ }
  simp [ProductionAdjacencyCacheSound, uncached]

/-- A bounded degree write preserves the complete relation, including the
unchanged adjacency cache and failure latch. This is a primitive carrier fact,
not an allocator phase theorem. -/
theorem ProductionStateRel.degree_write {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (node value : Nat)
    (bound : node < native.degrees.length) :
    ProductionStateRel {native with degrees := native.degrees.set node value}
      {production with degrees := production.degrees.set node value} := by
  exact { related with degrees :=
    CakeNodeMap.set_representsHOLNodeList _ _ related.degrees node value bound }

/-- Bounded parent writes preserve every other state component. -/
theorem ProductionStateRel.parent_write {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (node value : Nat)
    (bound : node < native.coalesced.length) :
    ProductionStateRel {native with coalesced := native.coalesced.set node value}
      {production with coalesced := production.coalesced.set node value} := by
  exact { related with parents :=
    CakeNodeMap.set_representsHOLNodeList _ _ related.parents node value bound }

/-- Bounded move-related writes preserve every other state component. -/
theorem ProductionStateRel.moveRelated_write {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (node : Nat) (value : Bool)
    (bound : node < native.move_related.length) :
    ProductionStateRel {native with move_related := native.move_related.set node value}
      {production with moveRelated := production.moveRelated.set node value} := by
  exact { related with moveRelated :=
    CakeNodeMap.set_representsHOLNodeList _ _ related.moveRelated node value bound }

end Flapjack.RegAlloc
