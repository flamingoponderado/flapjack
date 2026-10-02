import Flapjack.Compiler.Backend.RegAlloc.ProductionSpill
import Std.Data.TreeSet.Lemmas

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc

private theorem insertMembership (node member : Nat) (acc remaining : List Nat) :
    member ∈ sortedInsert node acc remaining ↔
      member ∈ acc ∨ member = node ∨ member ∈ remaining := by
  induction remaining generalizing acc with
  | nil => simp [sortedInsert, or_comm]
  | cons head rest ih =>
    by_cases equal : node = head
    · subst head
      simp [sortedInsert]
    · by_cases greater : node > head
      · simp [sortedInsert, equal, greater]
      · simp only [sortedInsert, equal, greater, if_false, ih, List.mem_cons]
        simp only [or_assoc, or_left_comm, or_comm]

/-- Actual adjacency insertion has the same membership as set insertion even
on an unsorted row. This infrastructure lemma is not a HOL invariant port;
ordered native adjacency transport and cache updates are separate obligations. -/
theorem cakeSortedInsert_membership (node member : Nat) (row : List Nat) :
    member ∈ cakeSortedInsert node row ↔ member = node ∨ member ∈ row := by
  simpa only [cakeSortedInsert, List.not_mem_nil, false_or] using insertMembership node member [] row

private def MapCacheRel (cache : CakeNodeMap (Std.TreeSet Nat)) (rows : CakeNodeMap (List Nat)) :=
  ∀ node neighbour, (cache.get node).map (fun set => set.contains neighbour) =
    (rows.get node).map (fun row => decide (neighbour ∈ row))

private theorem cache_default {cache : CakeNodeMap (Std.TreeSet Nat)}
    {rows : CakeNodeMap (List Nat)} (related : MapCacheRel cache rows) (node neighbour : Nat) :
    ((cache.get node).getD ∅).contains neighbour =
      decide (neighbour ∈ (rows.get node).getD []) := by
  have reads := related node neighbour
  cases cacheRead : cache.get node <;> cases rowRead : rows.get node <;> simp_all

private theorem insertEdge_cache {cache : CakeNodeMap (Std.TreeSet Nat)}
    {rows : CakeNodeMap (List Nat)} (related : MapCacheRel cache rows) (x y : Nat) :
    MapCacheRel (cakeInsertEdgeSet x y cache) (cakeInsertEdge x y rows) := by
  intro node neighbour
  unfold cakeInsertEdgeSet cakeInsertEdge cakeAdjSub
  by_cases atY : node = y
  · subst node
    simp only [CakeNodeMap.get_set_self, Option.map_some]
    simp only [Std.TreeSet.contains_insert, cakeSortedInsert_membership, Bool.decide_or,
      Bool.beq_eq_decide_eq, Std.LawfulEqCmp.compare_eq_iff_eq, cache_default related]
    simp only [eq_comm]
  · rw [CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm atY),
      CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm atY)]
    by_cases atX : node = x
    · subst node
      simp only [CakeNodeMap.get_set_self, Option.map_some]
      simp only [Std.TreeSet.contains_insert, cakeSortedInsert_membership, Bool.decide_or,
        Bool.beq_eq_decide_eq, Std.LawfulEqCmp.compare_eq_iff_eq, cache_default related]
      simp only [eq_comm]
    · rw [CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm atX),
        CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm atX)]
      exact related node neighbour

/-- The executed list and optional TreeSet edge updates preserve their cache
invariant at every key, including equal endpoints and missing/outside slots.
Both original rows are read before either write, as in the actual code. This
cache lemma is Flapjack infrastructure rather than native graph correctness. -/
theorem productionInsertEdge_cache (state : CakeRaState) (x y : Nat)
    (sound : ProductionAdjacencyCacheSound state) :
    ProductionAdjacencyCacheSound {state with
      adjLists := cakeInsertEdge x y state.adjLists
      adjSets := state.adjSets.map (cakeInsertEdgeSet x y)} := by
  cases cache : state.adjSets with
  | none => simp [ProductionAdjacencyCacheSound]
  | some sets =>
    simp only [ProductionAdjacencyCacheSound, cache] at sound
    exact insertEdge_cache sound x y

/-- One actual edge insertion matches native bounded subscript reads and both
list writes, preserving every state field and the optional query cache. Bounds
are input domains; no post-state or successful target evaluation is assumed.
This is cross-implementation infrastructure without a separate HOL original. -/
theorem insertEdge_production (x y : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production)
    (xBound : x < native.adj_ls.length) (yBound : y < native.adj_ls.length) :
    ∃ result, insertEdge x y native = (.success (), result) ∧
      result.adj_ls.length = native.adj_ls.length ∧
      ProductionStateRel result {production with
        adjLists := cakeInsertEdge x y production.adjLists
        adjSets := production.adjSets.map (cakeInsertEdgeSet x y)} := by
  let rowX := sortedInsert y [] native.adj_ls[x]
  let rowY := sortedInsert x [] native.adj_ls[y]
  let rows := (native.adj_ls.set x rowX).set y rowY
  refine ⟨{native with adj_ls := rows}, ?_, ?_, ?_⟩
  · simp only [insertEdge, Translator.Monadic.MonadBase.bind, adjLsSubEqn,
      if_pos xBound, if_pos yBound, Translator.Monadic.MonadBase.ignoreBind,
      updateAdjLsEqn, List.length_set, holEl_eq_getElem x native.adj_ls xBound,
      holEl_eq_getElem y native.adj_ls yBound]
    rfl
  · simp [rows]
  · refine {related with adjacency := ?_, adjacencyCache := productionInsertEdge_cache production x y related.adjacencyCache}
    have first := CakeNodeMap.set_representsHOLNodeList _ _ related.adjacency x rowX xBound
    have second := CakeNodeMap.set_representsHOLNodeList _ _ first y rowY (by simpa using yBound)
    simpa only [cakeInsertEdge, cakeAdjSub, related.adjacency_read x xBound,
      related.adjacency_read y yBound, Option.getD_some, cakeSortedInsert, rowX, rowY] using second

/-- Recursive actual edge insertion follows the native monadic traversal in
source order. The original bounded list supplies every read/write domain;
length preservation propagates those domains through intermediate states.
The optional cache is updated in lockstep, rather than dropped. -/
theorem listInsertEdge_production (x : Nat) (nodes : List Nat)
    {native : State} {production : CakeRaState} (related : ProductionStateRel native production)
    (xBound : x < native.adj_ls.length)
    (bounds : ∀ y ∈ nodes, y < native.adj_ls.length) :
    ∃ result, listInsertEdge x nodes native = (.success (), result) ∧
      result.adj_ls.length = native.adj_ls.length ∧
      ProductionStateRel result {production with
        adjLists := cakeListInsertEdge x nodes production.adjLists
        adjSets := production.adjSets.map (cakeListInsertEdgeSet x nodes)} := by
  induction nodes generalizing native production with
  | nil => exact ⟨native, rfl, rfl, by simpa [cakeListInsertEdge, cakeListInsertEdgeSet] using related⟩
  | cons node rest ih =>
    obtain ⟨first, firstRun, firstLength, firstRel⟩ :=
      insertEdge_production x node related xBound (bounds node (by simp))
    obtain ⟨result, tailRun, tailLength, tailRel⟩ := ih firstRel
      (by rwa [firstLength]) (by
        intro next member
        rw [firstLength]
        exact bounds next (List.mem_cons_of_mem node member))
    refine ⟨result, ?_, tailLength.trans firstLength, ?_⟩
    · simp only [listInsertEdge, Translator.Monadic.MonadBase.ignoreBind, firstRun, tailRun]
    · simpa only [cakeListInsertEdge, cakeListInsertEdgeSet, Option.map_map,
        Function.comp_def] using tailRel

end Flapjack.RegAlloc
