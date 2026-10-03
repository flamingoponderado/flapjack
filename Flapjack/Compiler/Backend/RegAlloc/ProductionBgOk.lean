import Flapjack.Compiler.Backend.RegAlloc.ProductionParentCompression

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- Bounded actual Fixed-colour queries agree with the native tag read. This
is actual/native query infrastructure, without a separate HOL original. -/
theorem isFixedK_production (limit node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) :
    isFixedK limit node native = (.success (cakeIsFixedK production limit node), native) := by
  have tagBound : node < native.node_tag.length := by rwa [good.2.1]
  have read := related.tag_read node tagBound
  cases tag : native.node_tag[node] <;>
    simp [isFixedK, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, tagBound,
      holEl_eq_getElem node native.node_tag tagBound, cakeIsFixedK, read, tag,
      Tag.toProduction, ret]

/-- Both original considered-variable reads are justified by the input
invariant; the actual constructor test gives the same Boolean. -/
theorem consideredVar_production (limit node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) :
    consideredVar limit node native = (.success (cakeConsideredVar production limit node), native) := by
  have tagBound : node < native.node_tag.length := by rwa [good.2.1]
  have read := related.tag_read node tagBound
  cases tag : native.node_tag[node] <;>
    simp [consideredVar, isAtemp, isFixedK, Translator.Monadic.MonadBase.bind,
      nodeTagSubEqn, tagBound, holEl_eq_getElem node native.node_tag tagBound,
      cakeConsideredVar, read, tag, Tag.toProduction, ret]

/-- Actual degree-or-limit queries preserve the native value and unchanged
state, with the degree domain derived from the original invariant. -/
theorem degOrInf_production (limit node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) :
    degOrInf limit node native = (.success (cakeDegOrInf production limit node), native) := by
  have degreeBound : node < native.degrees.length := by rwa [good.2.2.1]
  have read := related.degree_read node degreeBound
  have fixedRun := isFixedK_production limit node related good bound
  simp only [degOrInf, Translator.Monadic.MonadBase.bind, fixedRun]
  cases fixed : cakeIsFixedK production limit node <;>
    simp [fixed, cakeDegOrInf, degreesSubEqn, degreeBound,
      holEl_eq_getElem node native.degrees degreeBound, read, ret]

private theorem filter_pure {α : Type} (predicate : α → M State Bool StateException)
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

private theorem map_pure {α β : Type} (query : α → M State β StateException)
    (pure : α → β) (nodes : List α) (state : State)
    (reads : ∀ node ∈ nodes, query node state = (.success (pure node), state)) :
    stExMap query nodes state = (.success (nodes.map pure), state) := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    simp only [stExMap, Translator.Monadic.MonadBase.bind, reads node List.mem_cons_self,
      ih (fun next member => reads next (List.mem_cons_of_mem node member)), ret, List.map_cons]

private theorem filtered_bound (predicate : Nat → Bool) (nodes : List Nat) (dimension : Nat)
    (bounds : ∀ node ∈ nodes, node < dimension) :
    ∀ node ∈ filterReversed predicate nodes, node < dimension := by
  intro node member
  rw [filterReversed_production] at member
  exact bounds node (List.mem_filter.mp (List.mem_reverse.mp member)).1

private theorem mapped_count (query : Nat → Nat) (predicate : Nat → Bool) (nodes : List Nat) :
    ((nodes.map query).filter predicate).length = nodes.countP (fun node => predicate (query node)) := by
  rw [← List.countP_eq_length_filter, List.countP_map]
  rfl

/-- The whole actual George/Briggs criterion agrees with the native optional
case-list pair and leaves the native state unchanged. Original adjacency
domains derive every partition/filter/map bound; cached queries and reversed
filter order are preserved. This is actual/native infrastructure, not another
HOL bg_ok_success port or an assumed successful coalescing predicate. -/
theorem bgOk_production (limit x y : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (xBound : x < native.dim) (yBound : y < native.dim) :
    bgOk limit x y native = (.success (cakeBgOk limit x y production), native) := by
  have xRowBound : x < native.adj_ls.length := by rwa [good.1]
  have yRowBound : y < native.adj_ls.length := by rwa [good.1]
  let adjX := native.adj_ls[x]
  let adjY := native.adj_ls[y]
  have xRead := related.adjacency_read x xRowBound
  have yRead := related.adjacency_read y yRowBound
  have xQuery : ∀ node, cakeAdjMem production node x = sortedMem node adjX := by
    intro node
    simpa only [holEl_eq_getElem x native.adj_ls xRowBound] using cakeAdjMem_production node x related good xBound
  have yQuery : ∀ node, cakeAdjMem production node y = sortedMem node adjY := by
    intro node
    simpa only [holEl_eq_getElem y native.adj_ls yRowBound] using cakeAdjMem_production node y related good yBound
  have adjXBound : ∀ node ∈ adjX, node < native.dim :=
    good.2.2.2.2.2.2.1 adjX (List.getElem_mem xRowBound)
  have adjYBound : ∀ node ∈ adjY, node < native.dim :=
    good.2.2.2.2.2.2.1 adjY (List.getElem_mem yRowBound)
  let parts := holPartition (fun node => sortedMem node adjX) adjY
  let predicate := cakeConsideredVar production limit
  let case1 := filterReversed predicate parts.1
  let case2 := filterReversed predicate parts.2
  let case3 := filterReversed predicate (adjX.filter (fun node => !sortedMem node adjY))
  have raw1Bound : ∀ node ∈ parts.1, node < native.dim := by
    intro node member
    rcases (mem_holPart (fun node => sortedMem node adjX) adjY [] [] node).1 member with member | member
    · exact adjYBound node member
    · cases member
  have raw2Bound : ∀ node ∈ parts.2, node < native.dim := by
    intro node member
    rcases (mem_holPart (fun node => sortedMem node adjX) adjY [] [] node).2 member with member | member
    · exact adjYBound node member
    · cases member
  have raw3Bound : ∀ node ∈ adjX.filter (fun node => !sortedMem node adjY), node < native.dim := by
    intro node member
    exact adjXBound node (List.mem_filter.mp member).1
  have case1Bound := filtered_bound predicate parts.1 native.dim raw1Bound
  have case2Bound := filtered_bound predicate parts.2 native.dim raw2Bound
  have case3Bound := filtered_bound predicate _ native.dim raw3Bound
  have filterRun (nodes : List Nat) (bounds : ∀ node ∈ nodes, node < native.dim) :
      stExFilter (consideredVar limit) nodes [] native = (.success (filterReversed predicate nodes), native) := by
    simpa only [filterReversed_production, List.append_nil] using filter_pure (consideredVar limit)
      predicate nodes [] native (fun node member => consideredVar_production limit node related good (bounds node member))
  have firstFilter := filterRun parts.1 raw1Bound
  have secondFilter := filterRun parts.2 raw2Bound
  have thirdFilter := filterRun _ raw3Bound
  have firstMap := map_pure (degOrInf (limit + 1)) (cakeDegOrInf production (limit + 1)) case1 native
    (fun node member => degOrInf_production (limit + 1) node related good (case1Bound node member))
  have secondMap := map_pure (degOrInf limit) (cakeDegOrInf production limit) case2 native
    (fun node member => degOrInf_production limit node related good (case2Bound node member))
  have thirdMap := map_pure (degOrInf limit) (cakeDegOrInf production limit) case3 native
    (fun node member => degOrInf_production limit node related good (case3Bound node member))
  dsimp only [parts, adjX, adjY, predicate] at firstFilter secondFilter thirdFilter
  dsimp only [case1, case2, case3, parts, adjX, adjY, predicate] at firstMap secondMap thirdMap
  have actual : cakeBgOk limit x y production =
      (if case2.countP (fun node => cakeDegOrInf production limit node >= limit) = 0 then some (case1, case2)
       else if case1.countP (fun node => cakeDegOrInf production (limit + 1) node - 1 >= limit) +
         case2.countP (fun node => cakeDegOrInf production limit node >= limit) +
         case3.countP (fun node => cakeDegOrInf production limit node >= limit) < limit then some (case1, case2) else none) := by
    simp only [cakeBgOk, cakeAdjSub, xRead, yRead, Option.getD_some, xQuery, yQuery,
      partitionReversed_production]
    rfl
  rw [actual]
  simp only [bgOk, Translator.Monadic.MonadBase.bind, adjLsSubEqn, if_pos xRowBound,
    if_pos yRowBound, holEl_eq_getElem x native.adj_ls xRowBound, holEl_eq_getElem y native.adj_ls yRowBound]
  simp only [firstFilter, secondFilter, secondMap, mapped_count]
  split
  · rfl
  · simp only [Translator.Monadic.MonadBase.bind, thirdFilter, firstMap, thirdMap, ret, mapped_count]
    split <;> rfl

end Flapjack.RegAlloc
