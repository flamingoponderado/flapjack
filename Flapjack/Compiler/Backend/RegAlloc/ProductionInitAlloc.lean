import Flapjack.Compiler.Backend.RegAlloc.ProductionStep

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- The fused initializer's allocatable-tag test is exactly the original
bounded Atemp query. Missing-slot defaults are unreachable under the native
invariant and complete state relation. This is implementation correspondence,
not a duplicate HOL declaration. -/
theorem isAtemp_production (node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) :
    isAtemp node native =
      (.success ((production.nodeTag.get node).getD .aTemp == .aTemp), native) := by
  have tagBound : node < native.node_tag.length := by rwa [good.2.1]
  have read := related.tag_read node tagBound
  cases tag : native.node_tag[node] <;>
    simp [isAtemp, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, tagBound,
      holEl_eq_getElem node native.node_tag tagBound, read, tag, Tag.toProduction, ret] <;> rfl

private theorem stateFilter_pure {α : Type} (predicate : α → M State Bool StateException)
    (pure : α → Bool) (nodes acc : List α) (state : State)
    (reads : ∀ node ∈ nodes, predicate node state = (.success (pure node), state)) :
    stExFilter predicate nodes acc state = (.success ((nodes.filter pure).reverse ++ acc), state) := by
  induction nodes generalizing acc with
  | nil => rfl
  | cons node rest ih =>
    simp only [stExFilter, Translator.Monadic.MonadBase.bind, reads node List.mem_cons_self]
    cases selected : pure node <;>
      simp only [Bool.false_eq_true, if_false, if_true, List.filter_cons, selected,
        List.reverse_cons, List.append_assoc, List.singleton_append]
    all_goals exact ih _ (fun next member => reads next (List.mem_cons_of_mem node member))

/-- The original initializer's complete Atemp collection has the same reverse
order as the fused production traversal. All tag domains follow from COUNT_LIST
and the original state invariant. No desired collection is assumed. This
actual/native infrastructure has no separate HOL original. -/
theorem initAllocCollection_production {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    stExFilter isAtemp (List.range native.dim) [] native =
      (.success (((List.range native.dim).filter (fun node =>
        (production.nodeTag.get node).getD .aTemp == .aTemp)).reverse), native) := by
  simpa only [List.append_nil] using stateFilter_pure isAtemp
    (fun node => (production.nodeTag.get node).getD .aTemp == .aTemp)
    (List.range native.dim) [] native
    (fun node member => isAtemp_production node related good (List.mem_range.mp member))

/-- A whole original degree-initialization iteration corresponds to the
actual considered-neighbour count and bounded array write. Adjacency/tag
reads and every neighbour domain come from good_ra_state; the complete cache
and failure fields are retained. This is actual/native infrastructure. -/
theorem initAllocDegree_production (limit node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) :
    ∃ result,
      bind (adjLsSub node) (fun neighbours =>
        bind (stExFilter (fun neighbour => consideredVar limit neighbour) neighbours [])
          (fun fills => updateDegrees node fills.length)) native = (.success (), result) ∧
      goodRaState result ∧ native.dim = result.dim ∧
      ProductionStateRel result
        {production with
          degrees := production.degrees.set node
            (((production.adjLists.get node).getD []).filter (cakeConsideredVar production limit)).length} := by
  have adjacencyBound : node < native.adj_ls.length := by rwa [good.1]
  have degreeBound : node < native.degrees.length := by rwa [good.2.2.1]
  have read := related.adjacency_read node adjacencyBound
  let neighbours := native.adj_ls[node]
  let predicate := cakeConsideredVar production limit
  have neighbourBounds : ∀ neighbour ∈ neighbours, neighbour < native.dim :=
    fun neighbour member => good.2.2.2.2.2.2.1 neighbours
      (List.getElem_mem adjacencyBound) neighbour member
  have filterRun : stExFilter (fun neighbour => consideredVar limit neighbour) neighbours [] native =
      (.success (neighbours.filter predicate).reverse, native) := by
    simpa only [List.append_nil] using stateFilter_pure
      (fun neighbour => consideredVar limit neighbour) predicate neighbours [] native
      (fun neighbour member => consideredVar_production limit neighbour related good
        (neighbourBounds neighbour member))
  dsimp only [neighbours, predicate] at filterRun
  let result : State := {native with degrees := native.degrees.set node (neighbours.filter predicate).length}
  refine ⟨result, ?_, ?_, rfl, ?_⟩
  · simp only [Translator.Monadic.MonadBase.bind, adjLsSubEqn, if_pos adjacencyBound,
      holEl_eq_getElem node native.adj_ls adjacencyBound, filterRun,
      updateDegreesEqn, List.length_reverse, if_pos degreeBound]
    rfl
  · obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩ := good
    exact ⟨a,b,by simpa only [result, List.length_set] using c,d,e,f,g,h,i,j,k,l,m,n⟩
  · simpa only [read, Option.getD_some, neighbours, predicate, result] using
      related.degree_write node (neighbours.filter predicate).length degreeBound

/-- A complete self-parent initializer write retains good_ra_state and all
actual fields. This is the executed parent-write correspondence, not a second
port of do_upd_coalesce. -/
theorem initAllocParent_production (node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) :
    doUpdCoalesce node native =
      (.success (), {native with coalesced := native.coalesced.set node node}) ∧
    goodRaState {native with coalesced := native.coalesced.set node node} ∧
    ProductionStateRel {native with coalesced := native.coalesced.set node node}
      {production with coalesced := production.coalesced.set node node} := by
  have parentBound : node < native.coalesced.length := by rwa [good.2.2.2.1]
  refine ⟨?_, ?_, related.parent_write node node parentBound⟩
  · simp [doUpdCoalesce, updateCoalescedEqn, parentBound]
  · obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩ := good
    refine ⟨a,b,c,by simpa only [List.length_set] using d,e,?_,g,h,i,j,k,l,m,n⟩
    intro next member
    rcases List.mem_or_eq_of_mem_set member with member | rfl
    · exact f next member
    · exact bound

/-- Every original degree initializer action matches the actual degree fold;
all intermediate domains and good states are derived from the original bounds.
This is whole-traversal implementation infrastructure without a HOL tag. -/
theorem initAllocDegrees_production (limit : Nat) (nodes : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bounds : ∀ node ∈ nodes, node < native.dim) :
    ∃ result,
      stExForeach nodes (fun node => bind (adjLsSub node) (fun neighbours =>
        bind (stExFilter (fun neighbour => consideredVar limit neighbour) neighbours [])
          (fun fills => updateDegrees node fills.length))) native = (.success (), result) ∧
      goodRaState result ∧ native.dim = result.dim ∧
      ProductionStateRel result
        (nodes.foldl (fun state node =>
          {state with
            degrees := state.degrees.set node
              (((state.adjLists.get node).getD []).filter (cakeConsideredVar state limit)).length}) production) := by
  induction nodes generalizing native production with
  | nil => exact ⟨native, rfl, good, rfl, related⟩
  | cons node rest ih =>
    obtain ⟨step, stepRun, stepGood, stepDim, stepRel⟩ :=
      initAllocDegree_production limit node related good (bounds node List.mem_cons_self)
    have restBounds : ∀ next ∈ rest, next < step.dim := by
      intro next member
      rw [← stepDim]
      exact bounds next (List.mem_cons_of_mem node member)
    obtain ⟨result, run, resultGood, resultDim, represented⟩ := ih stepRel stepGood restBounds
    refine ⟨result, ?_, resultGood, stepDim.trans resultDim, ?_⟩
    · simp only [stExForeach, ignoreBind, stepRun, run]
    · simpa only [List.foldl_cons] using represented

/-- The full self-parent traversal corresponds to native do_upd_coalesce.
All array and list domains are derived from the input invariant and worklist
bounds. This is implementation infrastructure rather than a duplicate port. -/
theorem initAllocParents_production (nodes : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bounds : ∀ node ∈ nodes, node < native.dim) :
    ∃ result,
      stExForeach nodes doUpdCoalesce native = (.success (), result) ∧
      goodRaState result ∧ native.dim = result.dim ∧
      ProductionStateRel result
        (nodes.foldl (fun state node =>
          {state with coalesced := state.coalesced.set node node}) production) := by
  induction nodes generalizing native production with
  | nil => exact ⟨native, rfl, good, rfl, related⟩
  | cons node rest ih =>
    have step := initAllocParent_production node related good (bounds node List.mem_cons_self)
    have restBounds : ∀ next ∈ rest,
        next < ({native with coalesced := native.coalesced.set node node} : State).dim :=
      fun next member => bounds next (List.mem_cons_of_mem node member)
    obtain ⟨result, run, resultGood, resultDim, represented⟩ := ih step.2.2 step.2.1 restBounds
    refine ⟨result, ?_, resultGood, resultDim, ?_⟩
    · simp only [stExForeach, ignoreBind, step.1, run]
    · simpa only [List.foldl_cons] using represented

/-- The production degree seed traversal modifies only the degree map. This
unconditional implementation frame is used to justify reordering the fused
initializer's independent fields; it is not a HOL theorem. -/
theorem initAllocDegrees_frame (limit : Nat) (nodes : List Nat) (production : CakeRaState) :
    nodes.foldl (fun state node =>
      {state with
        degrees := state.degrees.set node
          (((state.adjLists.get node).getD []).filter (cakeConsideredVar state limit)).length}) production =
    {production with degrees := (nodes.foldl (fun state node =>
      {state with
        degrees := state.degrees.set node
          (((state.adjLists.get node).getD []).filter (cakeConsideredVar state limit)).length}) production).degrees} := by
  induction nodes generalizing production with
  | nil => rfl
  | cons node rest ih =>
    simp only [List.foldl_cons]
    rw [ih]

/-- Self-parent initialization changes only the coalescing map, including on
arbitrary production inputs. This is a concrete implementation frame, without
an independent HOL original. -/
theorem initAllocParents_frame (nodes : List Nat) (production : CakeRaState) :
    nodes.foldl (fun state node => {state with coalesced := state.coalesced.set node node}) production =
    {production with coalesced :=
      (nodes.foldl (fun state node => {state with coalesced := state.coalesced.set node node}) production).coalesced} := by
  induction nodes generalizing production with
  | nil => rfl
  | cons node rest ih =>
    simp only [List.foldl_cons]
    rw [ih]

/-- Complete flag clearing corresponds to native bounded updates, retaining
all other fields and the cache. It is used to account for the production fused
loop's early flag writes, not tagged as a separate source declaration. -/
theorem initAllocFlags_production (nodes : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production)
    (bounds : ∀ node ∈ nodes, node < native.move_related.length) :
    stExForeach nodes (fun node => updateMoveRelated node false) native =
      (.success (), {native with
        move_related := nodes.foldl (fun flags node => flags.set node false) native.move_related}) ∧
    ProductionStateRel
      {native with move_related := nodes.foldl (fun flags node => flags.set node false) native.move_related}
      {production with moveRelated := nodes.foldl (fun flags node => flags.set node false) production.moveRelated} := by
  induction nodes generalizing native production with
  | nil => exact ⟨rfl, related⟩
  | cons node rest ih =>
    have bound := bounds node List.mem_cons_self
    have nextRel := related.moveRelated_write node false bound
    have restBounds : ∀ next ∈ rest,
        next < ({native with move_related := native.move_related.set node false} : State).move_related.length := by
      intro next member
      simpa only [List.length_set] using bounds next (List.mem_cons_of_mem node member)
    have tail := ih nextRel restBounds
    refine ⟨?_, ?_⟩
    · simp only [stExForeach, ignoreBind, updateMoveRelatedEqn, if_pos bound, tail.1, List.foldl_cons]
    · simpa only [List.foldl_cons] using tail.2

/-- Clearing the full original node range represents the canonical replicated
false list. All dimensions are original invariant facts; the early fused flag
writes introduce no new domain or fallback. This is implementation evidence,
not another reset_move_related HOL port. -/
theorem initAllocFlags_range_production {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    stExForeach (List.range native.dim) (fun node => updateMoveRelated node false) native =
      (.success (), {native with move_related := List.replicate native.dim false}) ∧
    ProductionStateRel {native with move_related := List.replicate native.dim false}
      {production with
        moveRelated := (List.range native.dim).foldl
          (fun flags node => flags.set node false) production.moveRelated} := by
  have run := initAllocFlags_production (List.range native.dim) related
    (fun node member => by rw [good.2.2.2.2.1]; exact List.mem_range.mp member)
  have cleared : (List.range native.dim).foldl
      (fun flags node => flags.set node false) native.move_related = List.replicate native.dim false := by
    rw [← good.2.2.2.2.1, moveReset_list_range]
  simpa only [cleared] using run

/-- Literal body of the actual fused initializer, factored here only for its
proofs. This is Flapjack-specific implementation infrastructure: the HOL
initializer performs separate collection/degree/parent/flag traversals. -/
def initAllocFusedStep (initial : CakeRaState) (limit : Nat)
    (accumulator : List Nat × CakeRaState) (node : Nat) : List Nat × CakeRaState :=
  let (allocs, state) := accumulator
  let neighbours := (state.adjLists.get node).getD []
  let fills := neighbours.filter (cakeConsideredVar state limit)
  let allocs := if (initial.nodeTag.get node).getD .aTemp == .aTemp then node :: allocs else allocs
  (allocs, {state with
    degrees := state.degrees.set node fills.length
    coalesced := state.coalesced.set node node
    moveRelated := state.moveRelated.set node false})

/-- The fused collection has the source filter's exact reverse order even
before imposing native domains. No HOL declaration has this fused body. -/
theorem initAllocFused_collection (initial : CakeRaState) (limit : Nat)
    (nodes allocs : List Nat) (production : CakeRaState) :
    (nodes.foldl (initAllocFusedStep initial limit) (allocs, production)).1 =
      ((nodes.filter (fun node => (initial.nodeTag.get node).getD .aTemp == .aTemp)).reverse ++ allocs) := by
  induction nodes generalizing allocs production with
  | nil => rfl
  | cons node rest ih =>
    rw [List.foldl_cons, ih]
    simp only [initAllocFusedStep]
    cases selected : ((initial.nodeTag.get node).getD .aTemp == .aTemp) <;>
      simp [selected, List.reverse_cons, List.append_assoc]

/-- The fused body changes exactly three maps. This unconditional production
frame justifies separating the initializer operations; it is not a HOL port. -/
theorem initAllocFused_frame (initial : CakeRaState) (limit : Nat)
    (nodes allocs : List Nat) (production : CakeRaState) :
    (nodes.foldl (initAllocFusedStep initial limit) (allocs, production)).2 =
      {production with
        degrees := (nodes.foldl (initAllocFusedStep initial limit) (allocs, production)).2.degrees
        coalesced := (nodes.foldl (initAllocFusedStep initial limit) (allocs, production)).2.coalesced
        moveRelated := (nodes.foldl (initAllocFusedStep initial limit) (allocs, production)).2.moveRelated} := by
  induction nodes generalizing allocs production with
  | nil => rfl
  | cons node rest ih =>
    rw [List.foldl_cons, ih]
    rfl

/-- Fused self-parent writes are exactly the independent node-map fold.
This is a concrete implementation equation without a HOL original. -/
theorem initAllocFused_parents (initial : CakeRaState) (limit : Nat)
    (nodes allocs : List Nat) (production : CakeRaState) :
    (nodes.foldl (initAllocFusedStep initial limit) (allocs, production)).2.coalesced =
      nodes.foldl (fun parents node => parents.set node node) production.coalesced := by
  induction nodes generalizing allocs production with
  | nil => rfl
  | cons node rest ih =>
    rw [List.foldl_cons, ih, List.foldl_cons]
    rfl

/-- The fused clearing map is exactly the independent false-write fold;
the native full-range correspondence supplies its canonical representation.
This is actual implementation infrastructure, deliberately untagged. -/
theorem initAllocFused_flags (initial : CakeRaState) (limit : Nat)
    (nodes allocs : List Nat) (production : CakeRaState) :
    (nodes.foldl (initAllocFusedStep initial limit) (allocs, production)).2.moveRelated =
      nodes.foldl (fun flags node => flags.set node false) production.moveRelated := by
  induction nodes generalizing allocs production with
  | nil => rfl
  | cons node rest ih =>
    rw [List.foldl_cons, ih, List.foldl_cons]
    rfl

/-- Degree counting reads only the immutable graph and tag maps, so the fused
traversal equals the independent degree-map fold with those original reads.
No default or neighbour bound is assumed here; the native domain proof is in
initAllocDegrees_production. This is Flapjack-only implementation factoring. -/
theorem initAllocFused_degrees (initial : CakeRaState) (limit : Nat)
    (nodes allocs : List Nat) (production : CakeRaState) :
    (nodes.foldl (initAllocFusedStep initial limit) (allocs, production)).2.degrees =
      nodes.foldl (fun degrees node => degrees.set node
        (((production.adjLists.get node).getD []).filter (cakeConsideredVar production limit)).length)
        production.degrees := by
  induction nodes generalizing allocs production with
  | nil => rfl
  | cons node rest ih =>
    rw [List.foldl_cons, ih, List.foldl_cons]
    rfl

/-- The proved fused step is the body actually executed by the initializer,
not an independent proof-side algorithm. This equation preserves every actual
clause, including endpoint marking and both reversed partitions. Its source
counterpart uses separate native traversals, so this implementation equation
has no HOL tag. -/
theorem initAllocFused_equation (moves : List (Nat × (Nat × Nat))) (limit : Nat)
    (production : CakeRaState) :
    cakeInitAlloc1Heu moves limit production =
      let (allocs, initialized) := (List.range production.dim).foldl
        (initAllocFusedStep production limit) ([], production)
      let withMoves := {initialized with availMovesWl := cakeSortMoves moves}
      let withRelated := moves.foldl (fun state move =>
        let x := move.2.1
        let y := move.2.2
        let fixedX := cakeIsFixed state x
        let fixedY := cakeIsFixed state y
        let state := {state with moveRelated := state.moveRelated.set x (!fixedX)}
        {state with moveRelated := state.moveRelated.set y (!fixedY)}) withMoves
      let (low, high) := partitionReversed
        (fun node => cakeSplitDegree withRelated production.dim limit node) allocs
      let (freeze, simplify) := partitionReversed
        (fun node => cakeMoveRelatedSub withRelated node) low
      (allocs.length, {withRelated with spillWl := high, simpWl := simplify, freezeWl := freeze}) := by
  rfl

private theorem nodeMap_unique {α : Type} {left right : CakeNodeMap α} {values : List α}
    (leftRep : CakeNodeMap.RepresentsHOLNodeList left values)
    (rightRep : CakeNodeMap.RepresentsHOLNodeList right values) : left = right := by
  have outside : left.outside = right.outside := leftRep.1.trans rightRep.1.symm
  have slots : left.slots = right.slots := by
    apply Array.ext
    · exact leftRep.2.1.trans rightRep.2.1.symm
    · intro index leftBound rightBound
      have bound : index < values.length := by rwa [← leftRep.2.1]
      have reads := (leftRep.2.2 index bound).trans (rightRep.2.2 index bound).symm
      simpa only [CakeNodeMap.get, dif_pos leftBound, dif_pos rightBound] using reads
  cases left
  cases right
  cases slots
  cases outside
  rfl

/-- Full-range actual flag writes are exactly the canonical dense false map.
The original dimension and representation supply every bound; no desired map
is assumed. This is an implementation codec, not a HOL declaration. -/
theorem initAllocFlags_filled {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    (List.range native.dim).foldl (fun flags node => flags.set node false) production.moveRelated =
      CakeNodeMap.filled production.dim false := by
  have represented := (initAllocFlags_range_production related good).2.moveRelated
  have canonical := filled_representsHOLNodeList native.dim false
  rw [related.dimension]
  exact nodeMap_unique represented canonical

/-- The separate production degree traversal reads the original graph/tags
throughout. This unconditional field equation is Flapjack infrastructure. -/
theorem initAllocDegrees_projection (limit : Nat) (nodes : List Nat) (production : CakeRaState) :
    (nodes.foldl (fun state node =>
      {state with
        degrees := state.degrees.set node
          (((state.adjLists.get node).getD []).filter (cakeConsideredVar state limit)).length}) production).degrees =
    nodes.foldl (fun degrees node => degrees.set node
      (((production.adjLists.get node).getD []).filter (cakeConsideredVar production limit)).length)
      production.degrees := by
  induction nodes generalizing production with
  | nil => rfl
  | cons node rest ih =>
    rw [List.foldl_cons, ih, List.foldl_cons]
    rfl

/-- The separate parent traversal has exactly its node-map fold as payload.
This unconditional projection has no independent HOL original. -/
theorem initAllocParents_projection (nodes : List Nat) (production : CakeRaState) :
    (nodes.foldl (fun state node => {state with coalesced := state.coalesced.set node node}) production).coalesced =
      nodes.foldl (fun parents node => parents.set node node) production.coalesced := by
  induction nodes generalizing production with
  | nil => rfl
  | cons node rest ih => rw [List.foldl_cons, ih, List.foldl_cons]

/-- Complete state equality separating the executed fused initializer into
its independently checked degree and parent traversals and canonical clearing.
The equality retains graph/tag/cache/worklist/failure fields and derives flag
canonicality from the native invariant. This is implementation correspondence,
not a port of a separately fused HOL operation. -/
theorem initAllocFused_separate (limit : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ((List.range production.dim).foldl (initAllocFusedStep production limit) ([], production)).2 =
      let degrees := (List.range production.dim).foldl (fun state node =>
        {state with
          degrees := state.degrees.set node
            (((state.adjLists.get node).getD []).filter (cakeConsideredVar state limit)).length}) production
      let parents := (List.range production.dim).foldl
        (fun state node => {state with coalesced := state.coalesced.set node node}) degrees
      {parents with moveRelated := CakeNodeMap.filled production.dim false} := by
  rw [initAllocFused_frame, initAllocFused_degrees, initAllocFused_parents, initAllocFused_flags]
  have clearing := initAllocFlags_filled related good
  rw [related.dimension] at ⊢
  dsimp only
  rw [clearing]
  rw [initAllocParents_frame, initAllocParents_projection, initAllocDegrees_frame]
  simp only
  rw [initAllocDegrees_projection]
  simp only [related.dimension]

end Flapjack.RegAlloc
