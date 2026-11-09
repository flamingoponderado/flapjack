module

public import Flapjack.RiscV.Allocator

@[expose] public section

namespace Flapjack

/-!
The data model used by the CakeML graph-colouring allocator.

The executable spill allocator in Allocator.lean is deliberately small.  This
module ports the next layer of the source development: Fixed/Atemp/Stemp node
tags, the source-variable to graph-node bijection, and the graph builder that
interprets a clash tree as cliques.
-/

inductive WordRegTag where
  | fixed (colour : Nat)
  | atemp
  | stemp
  deriving DecidableEq, Repr

def wordTagColour : WordRegTag → Nat
  | .fixed colour => colour
  | .atemp | .stemp => 0

def wordIsStackVar (name : Nat) : Prop :=
  name % 4 = 3

def wordIsPhysicalVar (name : Nat) : Prop :=
  name % 2 = 0

def wordIsAllocVar (name : Nat) : Prop :=
  name % 4 = 1

def wordTagForSource (fixedSources : List Nat)
    (source : Nat) : WordRegTag :=
  let remainder := source % 4
  if remainder = 1 then
    if source ∈ fixedSources then .stemp else .atemp
  else if remainder = 3 then
    .stemp
  else
    .fixed (source / 2)

def wordMkTags (dimension : Nat) (fixedSources : List Nat)
    (fromNode : NatInfoMap Nat) : NatInfoMap WordRegTag :=
  (List.range dimension).map (fun node =>
    let source := match lookupNatInfo node fromNode with
      | some source => source
      | none => 0
    (node, wordTagForSource fixedSources source))

structure WordRegGraph where
  adjacency : NatInfoMap (List Nat)
  tags : NatInfoMap WordRegTag
  dimension : Nat
  deriving Repr

def wordGraphNeighbours (graph : WordRegGraph) (node : Nat) : List Nat :=
  match lookupNatInfo node graph.adjacency with
  | some neighbours => neighbours
  | none => []

def wordGraphUpdate (node : Nat) (neighbours : List Nat)
    (adjacency : NatInfoMap (List Nat)) : NatInfoMap (List Nat) :=
  (node, neighbours) :: adjacency.filter (fun entry => entry.1 != node)

def wordGraphInsertNeighbour (node neighbour : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  let current := wordGraphNeighbours graph node
  if neighbour ∈ current then
    graph
  else
    { graph with adjacency :=
        wordGraphUpdate node (neighbour :: current) graph.adjacency }

def wordGraphInsertEdge (left right : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  let graph := wordGraphInsertNeighbour left right graph
  wordGraphInsertNeighbour right left graph

def wordGraphInsertEdges (node : Nat) : List Nat →
    WordRegGraph → WordRegGraph
  | [], graph => graph
  | neighbour :: neighbours, graph =>
      wordGraphInsertEdges node neighbours
        (wordGraphInsertEdge node neighbour graph)

def wordGraphExtendClique : List Nat → List Nat → WordRegGraph →
    WordRegGraph × List Nat
  | [], clique, graph => (graph, clique)
  | node :: nodes, clique, graph =>
      if node ∈ clique then
        wordGraphExtendClique nodes clique graph
      else
        wordGraphExtendClique nodes (node :: clique)
          (wordGraphInsertEdges node clique graph)

def wordGraphInsertClique : List Nat → WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      wordGraphInsertClique nodes
        (wordGraphInsertEdges node nodes graph)

structure WordBijection where
  toNode : NatInfoMap Nat
  fromNode : NatInfoMap Nat
  next : Nat
  deriving Repr

def wordListRemap : List Nat → WordBijection → WordBijection
  | [], bijection => bijection
  | source :: sources, bijection =>
      match lookupNatInfo source bijection.toNode with
      | some _ => wordListRemap sources bijection
      | none =>
          wordListRemap sources
            { toNode := (source, bijection.next) :: bijection.toNode
              fromNode := (bijection.next, source) :: bijection.fromNode
              next := bijection.next + 1 }

def wordClashTreeBijection : WordClashTree → WordBijection →
    WordBijection
  | .delta writes reads, bijection =>
      wordListRemap writes (wordListRemap reads bijection)
  | .set names, bijection => wordListRemap names bijection
  | .branch branchLive thenBranch elseBranch, bijection =>
      let bijection := wordClashTreeBijection thenBranch bijection
      let bijection := wordClashTreeBijection elseBranch bijection
      match branchLive with
      | none => bijection
      | some names => wordListRemap names bijection
  | .seq first second, bijection =>
      wordClashTreeBijection first
        (wordClashTreeBijection second bijection)
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordMkBijection (tree : WordClashTree) : WordBijection :=
  wordClashTreeBijection tree
    { toNode := [], fromNode := [], next := 0 }

def wordBijectionToNode (bijection : WordBijection) (source : Nat) : Nat :=
  match lookupNatInfo source bijection.toNode with
  | some node => node
  | none => bijection.next

structure WordGraphResult where
  graph : WordRegGraph
  liveIn : List Nat
  deriving Repr

def wordMkGraph (toNode : Nat → Nat) : WordClashTree → List Nat →
    WordRegGraph → WordGraphResult
  | .delta writes reads, liveOut, graph =>
      let writes := writes.map toNode
      let reads := reads.map toNode
      let (graph, live) := wordGraphExtendClique writes liveOut graph
      let live := live.filter (fun node => node ∉ writes)
      let (graph, liveIn) := wordGraphExtendClique reads live graph
      { graph := graph, liveIn := liveIn }
  | .set names, _, graph =>
      let names := names.map toNode
      { graph := wordGraphInsertClique names graph, liveIn := names }
  | .branch branchLive thenBranch elseBranch, liveOut, graph =>
      let thenResult := wordMkGraph toNode thenBranch liveOut graph
      let elseResult :=
        wordMkGraph toNode elseBranch liveOut thenResult.graph
      match branchLive with
      | none =>
          let (graph, liveIn) := wordGraphExtendClique
            thenResult.liveIn elseResult.liveIn elseResult.graph
          { graph := graph, liveIn := liveIn }
      | some names =>
          let names := names.map toNode
          { graph := wordGraphInsertClique names elseResult.graph
            liveIn := names }
  | .seq first second, liveOut, graph =>
      let secondResult := wordMkGraph toNode second liveOut graph
      wordMkGraph toNode first secondResult.liveIn secondResult.graph
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordTagFixedColour : WordRegTag → Option Nat
  | .fixed colour => some colour
  | .atemp | .stemp => none

def wordFixedNeighbourColours (nodes : List Nat)
    (tags : NatInfoMap WordRegTag) : List Nat :=
  match nodes with
  | [] => []
  | node :: nodes =>
      let colours := match lookupNatInfo node tags with
        | some tag =>
            match wordTagFixedColour tag with
            | some colour => [colour]
            | none => []
        | none => []
      colours ++ wordFixedNeighbourColours nodes tags

def wordRemoveColours (removed colours : List Nat) : List Nat :=
  match colours with
  | [] => []
  | colour :: colours =>
      if colour ∈ removed then
        wordRemoveColours removed colours
      else
        colour :: wordRemoveColours removed colours

def wordStackColourCandidates (start : Nat) (blocked : List Nat) : List Nat :=
  (List.range (start + blocked.length + 1)).filter
    (fun colour => colour ≥ start)

def wordUnboundColour (start : Nat) (blocked : List Nat) : Nat :=
  match wordFirstAvailable (wordStackColourCandidates start blocked) blocked with
  | some colour => colour
  | none => start

def wordGraphUpdateTag (node : Nat) (tag : WordRegTag)
    (tags : NatInfoMap WordRegTag) : NatInfoMap WordRegTag :=
  (node, tag) :: tags.filter (fun entry => entry.1 != node)

def wordAssignAtempTag (colours : List Nat) (node : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  match lookupNatInfo node graph.tags with
  | some .atemp =>
      let blocked := wordFixedNeighbourColours
        (wordGraphNeighbours graph node) graph.tags
      match wordFirstAvailable (wordRemoveColours blocked colours) blocked with
      | some colour =>
          { graph with tags := wordGraphUpdateTag node (.fixed colour) graph.tags }
      | none =>
          { graph with tags := wordGraphUpdateTag node .stemp graph.tags }
  | some (.fixed _) | some .stemp | none => graph

def wordAssignAtemps (colours : List Nat) : List Nat →
    WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      wordAssignAtemps colours nodes (wordAssignAtempTag colours node graph)

def wordAssignStempTag (stackStart : Nat) (node : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  match lookupNatInfo node graph.tags with
  | some .stemp =>
      let blocked := wordFixedNeighbourColours
        (wordGraphNeighbours graph node) graph.tags
      let colour := wordUnboundColour stackStart blocked
      { graph with tags :=
          wordGraphUpdateTag node (.fixed colour) graph.tags }
  | some (.fixed _) | some .atemp | none => graph

def wordAssignStemps (stackStart : Nat) : List Nat →
    WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      wordAssignStemps stackStart nodes
        (wordAssignStempTag stackStart node graph)

def wordColourGraph (dimension colours stackStart : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  let nodes := List.range dimension
  let colours := (List.range colours).map (fun colour => colour + 1)
  let graph := wordAssignAtemps colours nodes graph
  wordAssignStemps stackStart nodes graph

def wordGraphTagColour (graph : WordRegGraph) (node : Nat) : Option Nat :=
  match lookupNatInfo node graph.tags with
  | some tag => wordTagFixedColour tag
  | none => none

def wordGraphTagsAreFixed (graph : WordRegGraph) : Bool :=
  graph.tags.all (fun entry =>
    match entry.2 with
    | .fixed _ => true
    | .atemp | .stemp => false)

def wordGraphColouringRespectsEdges (graph : WordRegGraph) : Bool :=
  graph.adjacency.all (fun entry =>
    let node := entry.1
    entry.2.all (fun neighbour =>
      match wordGraphTagColour graph node,
        wordGraphTagColour graph neighbour with
      | some left, some right => left != right
      | _, _ => false))

structure WordRaState where
  graph : WordRegGraph
  active : List Nat
  degrees : NatInfoMap Nat
  simpWl : List Nat
  spillWl : List Nat
  stack : List Nat
  deriving Repr

def wordRaNodeIsAtemp (graph : WordRegGraph) (node : Nat) : Bool :=
  match lookupNatInfo node graph.tags with
  | some .atemp => true
  | some (.fixed _) | some .stemp | none => false

def wordRaNodeIsStemp (graph : WordRegGraph) (node : Nat) : Bool :=
  match lookupNatInfo node graph.tags with
  | some .stemp => true
  | some (.fixed _) | some .atemp | none => false

def wordRaDegree (graph : WordRegGraph) (node : Nat) : Nat :=
  (wordGraphNeighbours graph node).length

def wordRaDegrees (graph : WordRegGraph) : NatInfoMap Nat :=
  (List.range graph.dimension).map (fun node => (node, wordRaDegree graph node))

def wordRaRefreshWorklists (colours : Nat) (state : WordRaState) :
    WordRaState :=
  let simpWl := state.active.filter (fun node =>
    wordRaNodeIsAtemp state.graph node &&
      match lookupNatInfo node state.degrees with
      | some degree => degree < colours
      | none => false)
  let spillWl := state.active.filter (fun node =>
    wordRaNodeIsAtemp state.graph node &&
      match lookupNatInfo node state.degrees with
      | some degree => degree ≥ colours
      | none => false)
  { state with simpWl := simpWl, spillWl := spillWl }

def wordRaInit (colours : Nat) (graph : WordRegGraph) : WordRaState :=
  let active := List.range graph.dimension
  let state : WordRaState :=
    { graph := graph
      active := active
      degrees := wordRaDegrees graph
      simpWl := []
      spillWl := []
      stack := [] }
  wordRaRefreshWorklists colours state

def wordRaDegreesForActive (graph : WordRegGraph)
    (active : List Nat) : NatInfoMap Nat :=
  active.map (fun node =>
    (node, ((wordGraphNeighbours graph node).filter
      (fun neighbour => active.contains neighbour)).length))

def wordRaInitFromStack (colours : Nat) (preStack : List Nat)
    (graph : WordRegGraph) : WordRaState :=
  let active := (List.range graph.dimension).filter
    (fun node => !preStack.contains node)
  let state : WordRaState :=
    { graph := graph
      active := active
      degrees := wordRaDegreesForActive graph active
      simpWl := []
      spillWl := []
      stack := preStack }
  wordRaRefreshWorklists colours state

def wordRaPartitionBy (predicate : Nat → Bool) : List Nat →
    List Nat × List Nat
  | [] => ([], [])
  | node :: nodes =>
      let (yes, no) := wordRaPartitionBy predicate nodes
      if predicate node then
        (node :: yes, no)
      else
        (yes, node :: no)

/- Move spill candidates that have become low degree into the simplify
   worklist. This is the register-side part of CakeML unspill; move revival
   is handled by WordMoveState after coalescing. -/
def wordRaUnspill (colours : Nat) (state : WordRaState) : WordRaState :=
  let (low, high) := wordRaPartitionBy (fun node =>
    (lookupNatInfo node state.degrees).getD 0 < colours) state.spillWl
  { state with
    simpWl := low ++ state.simpWl
    spillWl := high }

def wordRaRemoveNode (colours : Nat) (node : Nat)
    (_forceSpill : Bool) (state : WordRaState) : WordRaState :=
  let graph := state.graph
  let degrees := (wordGraphNeighbours state.graph node).foldl
    (fun degrees neighbour =>
      match lookupNatInfo neighbour degrees with
      | some degree =>
          (neighbour, degree - 1) :: degrees.filter
            (fun entry => entry.1 != neighbour)
      | none => degrees)
    state.degrees
  let state := { state with
    graph := graph
    active := state.active.erase node
    degrees := degrees
    simpWl := state.simpWl.erase node
    spillWl := state.spillWl.erase node
    stack := node :: state.stack }
  wordRaUnspill colours state

def wordRaChooseSpillNodeByDegree (degrees : NatInfoMap Nat) :
    Nat → List Nat → Nat
  | node, [] => node
  | node, candidate :: candidates =>
      let best := wordRaChooseSpillNodeByDegree degrees node candidates
      let candidateDegree := (lookupNatInfo candidate degrees).getD 0
      let bestDegree := (lookupNatInfo best degrees).getD 0
      if bestDegree < candidateDegree then candidate else best

def wordRaSimplifyAll : Nat → Nat → WordRaState → WordRaState
  | 0, _, state => state
  | fuel + 1, colours, state =>
      match state.simpWl with
      | node :: _ =>
          wordRaSimplifyAll fuel colours
            (wordRaRemoveNode colours node false state)
      | [] =>
          match state.spillWl with
          | node :: nodes =>
              let chosen := wordRaChooseSpillNodeByDegree state.degrees node nodes
              wordRaSimplifyAll fuel colours
                (wordRaRemoveNode colours chosen true state)
          | [] => state

def wordRaSimplifyLow : Nat → Nat → WordRaState → WordRaState
  | 0, _, state => state
  | fuel + 1, colours, state =>
      match state.simpWl with
      | node :: _ =>
          wordRaSimplifyLow fuel colours
            (wordRaRemoveNode colours node false state)
      | [] => state

def wordRaInitialSimplify (colours : Nat)
    (graph : WordRegGraph) : WordRaState :=
  let state := wordRaInit colours graph
  wordRaSimplifyLow (state.active.length + 1) colours state

def wordRaFinalizeStemps (state : WordRaState) : WordRaState :=
  let stempNodes := state.active.filter (wordRaNodeIsStemp state.graph)
  { state with
    active := state.active.filter (fun node => !wordRaNodeIsStemp state.graph node)
    stack := stempNodes.reverse ++ state.stack }

def wordRaChooseColour (colours stackStart : Nat)
    (graph : WordRegGraph) (node : Nat) : Nat :=
  let blocked := wordFixedNeighbourColours
    (wordGraphNeighbours graph node) graph.tags
  match lookupNatInfo node graph.tags with
  | some .stemp => wordUnboundColour stackStart blocked
  | some .atemp =>
      match wordFirstAvailable
          (wordRemoveColours blocked
            ((List.range colours).map (fun colour => colour + 1))) blocked with
      | some colour => colour
      | none => wordUnboundColour stackStart blocked
  | some (.fixed colour) => colour
  | none => 0

def wordRaAtempHasAvailableColour (colours : Nat)
    (graph : WordRegGraph) (node : Nat) : Bool :=
  let blocked := wordFixedNeighbourColours
    (wordGraphNeighbours graph node) graph.tags
  (wordFirstAvailable
    (wordRemoveColours blocked ((List.range colours).map (fun colour => colour + 1))) blocked).isSome

def wordRaMarkUncolourableAtemp (colours : Nat)
    (graph : WordRegGraph) (node : Nat) : WordRegGraph :=
  match lookupNatInfo node graph.tags with
  | some .atemp =>
      if wordRaAtempHasAvailableColour colours graph node then graph
      else 
        { graph with tags := wordGraphUpdateTag node .stemp graph.tags }
  | some (.fixed _) | some .stemp | none => graph

def wordRaColourStack (colours stackStart : Nat) :
    List Nat → WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      let graph := wordRaMarkUncolourableAtemp colours graph node
      let colour := wordRaChooseColour colours stackStart graph node
      let graph := { graph with
        tags := wordGraphUpdateTag node (.fixed colour) graph.tags }
      wordRaColourStack colours stackStart nodes graph

def wordColourGraphWithWorklist (colours stackStart : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  let state := wordRaInit colours graph
  let state := wordRaSimplifyAll (state.active.length + 1) colours state
  let state := wordRaFinalizeStemps state
  wordRaColourStack colours stackStart state.stack state.graph

/-! Move worklists and the first coalescing step.

    CakeML keeps move preferences separate from clash edges.  A move is first
    rejected when it is reflexive, already clashes, or has two fixed
    endpoints.  The remaining moves are canonicalised so a fixed endpoint is
    always the coalescing target.  The full CakeML allocator has additional
    freeze and move-revival phases; this section ports the data and the safe
    coalescing transition those phases build on.
-/

def wordTagIsFixed : WordRegTag → Bool
  | .fixed _ => true
  | .atemp | .stemp => false

def wordTagIsAtemp : WordRegTag → Bool
  | .atemp => true
  | .fixed _ | .stemp => false

def wordGraphTagIs (predicate : WordRegTag → Bool)
    (graph : WordRegGraph) (node : Nat) : Bool :=
  match lookupNatInfo node graph.tags with
  | some tag => predicate tag
  | none => false

def wordGraphTagFixedBelow (colours : Nat) (graph : WordRegGraph)
    (node : Nat) : Bool :=
  match lookupNatInfo node graph.tags with
  | some (.fixed colour) => colour < colours
  | some .atemp | some .stemp | none => false

def wordPartitionBy (predicate : Nat → Bool) : List Nat →
    List Nat × List Nat
  | [] => ([], [])
  | node :: nodes =>
      let (yes, no) := wordPartitionBy predicate nodes
      if predicate node then
        (node :: yes, no)
      else
        (yes, node :: no)

def wordConsideredVar (colours : Nat) (graph : WordRegGraph)
    (node : Nat) : Bool :=
  wordGraphTagIs wordTagIsAtemp graph node ||
    wordGraphTagFixedBelow colours graph node

def wordDegreeOrInf (colours : Nat) (graph : WordRegGraph)
    (node : Nat) : Nat :=
  if wordGraphTagFixedBelow colours graph node then
    colours
  else
    wordRaDegree graph node

def wordBgOk (colours : Nat) (graph : WordRegGraph)
    (target absorbed : Nat) : Option (List Nat × List Nat) :=
  let targetNeighbours := wordGraphNeighbours graph target
  let absorbedNeighbours := wordGraphNeighbours graph absorbed
  let (case1, case2) := wordPartitionBy
    (fun node => targetNeighbours.contains node) absorbedNeighbours
  let case1 := case1.filter (wordConsideredVar colours graph)
  let case2 := case2.filter (wordConsideredVar colours graph)
  let case2Degrees := case2.filter (fun node =>
    wordDegreeOrInf colours graph node ≥ colours)
  let case2Length := case2Degrees.length
  if case2Length = 0 then
    some (case1, case2)
  else
    let case3 := targetNeighbours.filter (fun node =>
      !(absorbedNeighbours.contains node) &&
        wordConsideredVar colours graph node)
    let case1Degrees := case1.map (wordDegreeOrInf (colours + 1) graph)
    let case3Degrees := case3.map (wordDegreeOrInf colours graph)
    let case1Length := (case1Degrees.filter (fun degree =>
      degree - 1 ≥ colours)).length
    let case3Length := (case3Degrees.filter (fun degree =>
      degree ≥ colours)).length
    if case1Length + case2Length + case3Length < colours then
      some (case1, case2)
    else
      none

def wordParentUpdate (node parent : Nat)
    (parents : NatInfoMap Nat) : NatInfoMap Nat :=
  (node, parent) :: parents.filter (fun entry => entry.1 != node)

def wordParentOf (parents : NatInfoMap Nat) (node : Nat) : Nat :=
  match lookupNatInfo node parents with
  | some parent => parent
  | none => node

/- A CakeML freeze candidate is a live Atemp that is still move-related and
   has degree below the register budget.  Fixed nodes and coalesced nodes stay
   out of this worklist. -/
def wordMoveFreezeCandidates (colours : Nat) (graph : WordRegGraph)
    (parents : NatInfoMap Nat) (related : List Nat) : List Nat :=
  (List.range graph.dimension).filter (fun node =>
    wordParentOf parents node = node &&
      wordGraphTagIs wordTagIsAtemp graph node &&
      wordRaDegree graph node < colours && related.contains node)

def wordCoalesceParentFuel : Nat → WordRegGraph → NatInfoMap Nat → Nat →
    Nat × NatInfoMap Nat
  | 0, _graph, parents, node => (wordParentOf parents node, parents)
  | fuel + 1, graph, parents, node =>
      let parent := wordParentOf parents node
      if parent = node then
        (node, parents)
      else if wordGraphTagIs wordTagIsFixed graph parent then
        (parent, parents)
      else if node ≤ parent then
        (node, parents)
      else
        let (ancestor, parents) :=
          wordCoalesceParentFuel fuel graph parents parent
        (ancestor, wordParentUpdate node ancestor parents)

def wordRaFirstMatchingFixedColour (available : List Nat)
    (graph : WordRegGraph) : List Nat → Option Nat
  | [] => none
  | node :: nodes =>
      match lookupNatInfo node graph.tags with
      | some (.fixed colour) =>
          if colour ∈ available then some colour
          else wordRaFirstMatchingFixedColour available graph nodes
      | some .atemp | some .stemp | none =>
          wordRaFirstMatchingFixedColour available graph nodes

def wordMoveFreezeCandidatesForActive (colours : Nat)
    (graph : WordRegGraph) (active : List Nat)
    (degrees : NatInfoMap Nat) (parents : NatInfoMap Nat)
    (related : List Nat) : List Nat :=
  active.filter (fun node =>
    wordParentOf parents node = node &&
      wordGraphTagIs wordTagIsAtemp graph node &&
      (lookupNatInfo node degrees).getD 0 < colours &&
      related.contains node)

def wordMoveSpillCandidatesForActive (colours : Nat)
    (graph : WordRegGraph) (active : List Nat)
    (degrees : NatInfoMap Nat) : List Nat :=
  active.filter (fun node =>
    wordGraphTagIs wordTagIsAtemp graph node &&
      (lookupNatInfo node degrees).getD 0 >= colours)

def wordCoalesceFreshNeighbours (graph : WordRegGraph)
    (target absorbed : Nat) : List Nat :=
  (wordGraphNeighbours graph absorbed).filter (fun node =>
    node != target && !(wordGraphNeighbours graph target).contains node)

def wordCoalesceSignificant (colours : Nat) (graph : WordRegGraph)
    (node : Nat) : Bool :=
  match lookupNatInfo node graph.tags with
  | some (.fixed _) => true
  | some .atemp | some .stemp => wordRaDegree graph node ≥ colours
  | none => true

/- Revive unavailable moves incident on neighbors whose degree may have
   decreased after a coalescing step. This is the CakeML revive_moves phase:
   revived moves return to the priority-sorted available worklist. -/
def wordMoveSetDegree (node degree : Nat)
    (degrees : NatInfoMap Nat) : NatInfoMap Nat :=
  (node, degree) :: degrees.filter (fun entry => entry.1 != node)

def wordMoveIncDegree (node amount : Nat)
    (degrees : NatInfoMap Nat) : NatInfoMap Nat :=
  match lookupNatInfo node degrees with
  | some degree => wordMoveSetDegree node (degree + amount) degrees
  | none => degrees

def wordMoveDecDegree (node : Nat)
    (degrees : NatInfoMap Nat) : NatInfoMap Nat :=
  match lookupNatInfo node degrees with
  | some degree => wordMoveSetDegree node (degree - 1) degrees
  | none => degrees

def wordMoveDecNeighbours (graph : WordRegGraph) (node : Nat)
    (degrees : NatInfoMap Nat) : NatInfoMap Nat :=
  (wordGraphNeighbours graph node).foldl
    (fun degrees neighbour => wordMoveDecDegree neighbour degrees) degrees

/-! Repeated coalescing mirrors CakeML's do_coalesce loop.  Invalid moves
    are retired to the unavailable list, while a successful merge rebuilds
    the pending worklists so moves that became useful are reconsidered. -/

structure WordRegAllocInput where
  bijection : WordBijection
  graph : WordRegGraph
  deriving Repr

def wordInitRegAlloc (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat) :
    WordRegAllocInput :=
  let bijection := wordMkBijection tree
  let emptyGraph : WordRegGraph :=
    { adjacency := [], tags := [], dimension := bijection.next }
  let graphResult := wordMkGraph
    (wordBijectionToNode bijection) tree [] emptyGraph
  let graph := forced.foldl
    (fun graph edge =>
      wordGraphInsertEdge
        (wordBijectionToNode bijection edge.1)
        (wordBijectionToNode bijection edge.2) graph)
    graphResult.graph
  { bijection := bijection
    graph := { graph with
      tags := wordMkTags bijection.next fixedSources bijection.fromNode } }

/-! Bridge the graph allocator back to source variables.

    CakeML stores compressed graph colours and applies total_colour only at
    the Word boundary.  In particular, physical source variables are tagged
    with half their architectural register number and total colours are
    doubled again.  Keeping this conversion explicit avoids accidentally
    treating a graph colour as a RISC-V register number. -/

def wordGraphNodeFinalColour (graph : WordRegGraph)
    (parents : NatInfoMap Nat) (node : Nat) : Nat :=
  let (root, _) := wordCoalesceParentFuel
    (graph.dimension + 1) graph parents node
  match wordGraphTagColour graph root with
  | some colour => colour
  | none => 0

def wordGraphTotalColourAt (graph : WordRegGraph)
    (parents : NatInfoMap Nat) (node : Nat) : Nat :=
  2 * wordGraphNodeFinalColour graph parents node

def wordGraphColouringAt (colouring : NatInfoMap Nat)
    (source : Nat) : Nat :=
  match lookupNatInfo source colouring with
  | some colour => colour
  | none => if source % 2 == 0 then source else 0

def wordGraphTotalColouring (input : WordRegAllocInput)
    (graph : WordRegGraph) (parents : NatInfoMap Nat) : NatInfoMap Nat :=
  input.bijection.fromNode.map (fun entry =>
    (entry.2, wordGraphTotalColourAt graph parents entry.1))

structure WordGraphAllocation where
  bijection : WordBijection
  initialTags : NatInfoMap WordRegTag
  graph : WordRegGraph
  colouring : NatInfoMap Nat
  parents : NatInfoMap Nat
  deriving Repr

/-! Cost-aware spill selection from CakeML `do_spill`.  The heuristic
    costs are keyed by source names, while the graph worklist operates on
    bijection nodes, so translate the finite map once at allocation setup. -/
def wordSpillCostsToNodes (bijection : WordBijection)
    (costs : NatInfoMap Nat) : NatInfoMap Nat :=
  costs.foldl (fun result entry =>
    match lookupNatInfo entry.1 bijection.toNode with
    | some node => (node, entry.2) :: result
    | none => result) []

def wordRaSpillCost (costs : NatInfoMap Nat) (node : Nat) : Nat :=
  (lookupNatInfo node costs).getD 0

/-! CakeML's `safe_div` ranks a spill candidate by its cost divided by
    its current degree.  The degree map is the mutable active-graph degree
    maintained by the worklist state. -/
def wordRaSafeDiv (numerator denominator : Nat) : Nat :=
  if denominator = 0 then 0 else numerator / denominator

def wordRaSpillPriority (costs degrees : NatInfoMap Nat) (node : Nat) : Nat :=
  wordRaSafeDiv (wordRaSpillCost costs node)
    ((lookupNatInfo node degrees).getD 0)

def wordRaChooseSpillNode (costs degrees : NatInfoMap Nat) : Nat → List Nat → Nat
  | node, [] => node
  | node, candidate :: candidates =>
      let best := wordRaChooseSpillNode costs degrees node candidates
      if wordRaSpillPriority costs degrees candidate <
          wordRaSpillPriority costs degrees best then
        candidate
      else
        best

def wordRaSimplifyAllWithSpillCosts : Nat → Nat → NatInfoMap Nat →
    WordRaState → WordRaState
  | 0, _, _, state => state
  | fuel + 1, colours, costs, state =>
      match state.simpWl with
      | node :: _ =>
          wordRaSimplifyAllWithSpillCosts fuel colours costs
            (wordRaRemoveNode colours node false state)
      | [] =>
          match state.spillWl with
          | [] => state
          | node :: nodes =>
              let chosen := wordRaChooseSpillNode costs state.degrees node nodes
              wordRaSimplifyAllWithSpillCosts fuel colours costs
                (wordRaRemoveNode colours chosen true state)

def wordGraphCheckAllocation (tree : WordClashTree)
    (candidate : WordGraphAllocation) : Option WordGraphAllocation :=
  let colour := wordGraphColouringAt candidate.colouring
  if wordGraphTagsAreFixed candidate.graph &&
      wordGraphColouringRespectsEdges candidate.graph &&
      (wordClashTreeCheck colour tree [] []).isSome then
    some candidate
  else
    none

theorem wordGraphCheckAllocation_sound
    (tree : WordClashTree) (allocation : WordGraphAllocation)
    (hcheck : wordGraphCheckAllocation tree allocation = some allocation) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        tree [] []).isSome = true := by
  have hcheck' :
      wordGraphTagsAreFixed allocation.graph = true ∧
        wordGraphColouringRespectsEdges allocation.graph = true ∧
        wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
          tree [] [] ≠ none := by
    simpa [wordGraphCheckAllocation] using hcheck
  rcases hcheck' with ⟨hfixed, hedges, hnotnone⟩
  have htree :
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        tree [] []).isSome = true := by
    cases hresult : wordClashTreeCheck
        (wordGraphColouringAt allocation.colouring) tree [] [] with
    | none => exact (hnotnone hresult).elim
    | some value => simp
  exact ⟨hfixed, hedges, htree⟩

/-! Backward forced-stack analysis from CakeML's get_stack_only.  The two
    lists correspond to its temporary-stack and forced-stack sets.  Lists are
    used as finite sets here so the analysis remains executable and easy to
    inspect in small RISC-V allocation regressions. -/

structure WordStackOnlyState where
  temporary : List Nat
  forced : List Nat
  deriving DecidableEq, Repr

def wordStackOnlyInsert (name : Nat) (names : List Nat) : List Nat :=
  if name ∈ names then names else name :: names

def wordStackOnlyDelete (name : Nat) (names : List Nat) : List Nat :=
  names.filter (fun candidate => candidate != name)

def wordStackOnlyUnion (left right : List Nat) : List Nat :=
  right.foldl (fun names name => wordStackOnlyInsert name names) left

def wordStackOnlyIntersection (left right : List Nat) : List Nat :=
  left.filter (fun name => name ∈ right)

def wordStackOnlyDifference (left right : List Nat) : List Nat :=
  left.filter (fun name => name ∉ right)

def wordStackOnlyRemoveTemps (names : List Nat)
    (state : WordStackOnlyState) : WordStackOnlyState :=
  let temporary := names.foldl
    (fun temporary name => wordStackOnlyDelete name temporary)
    state.temporary
  { state with temporary := temporary }

def wordStackOnlyMergeMove (destination source : Nat)
    (state : WordStackOnlyState) : WordStackOnlyState :=
  if destination ∈ state.temporary then
    let temporary := if source % 4 = 1 then
      wordStackOnlyInsert source state.temporary else state.temporary
    let forced := if source % 2 = 0 then state.forced
      else wordStackOnlyInsert destination state.forced
    { temporary := temporary
      forced := forced }
  else if destination % 4 = 3 then
    let temporary := if source % 4 = 1 then
      wordStackOnlyInsert source state.temporary else state.temporary
    { temporary := temporary
      forced := state.forced }
  else
    { state with temporary := wordStackOnlyDelete source state.temporary }

def wordStackOnlyMergeBranches (base left right : WordStackOnlyState) :
    WordStackOnlyState :=
  let keep := wordStackOnlyIntersection right.temporary
    (wordStackOnlyIntersection left.temporary base.temporary)
  let newOnly := wordStackOnlyUnion
    (wordStackOnlyDifference left.temporary base.temporary)
    (wordStackOnlyDifference right.temporary base.temporary)
  { temporary := wordStackOnlyUnion keep newOnly
    forced := wordStackOnlyUnion left.forced right.forced }

end Flapjack
