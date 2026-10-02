import Flapjack.Compiler.Backend.RegAlloc.ProductionMoveTable

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

private theorem good_tag_write {native : State} (good : goodRaState native)
    (node : Nat) (tag : Tag) : goodRaState {native with node_tag := native.node_tag.set node tag} := by
  obtain ⟨g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14⟩ := good
  exact ⟨g1, (List.length_set ..).trans g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14⟩

private theorem write_production (node : Nat) (tag : Tag)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.node_tag.length) :
    ∃ result, updateNodeTag node tag native = (.success (), result) ∧
      goodRaState result ∧ native.dim = result.dim ∧
      ProductionStateRel result {production with nodeTag := production.nodeTag.set node tag.toProduction} := by
  exact ⟨_, by simp [updateNodeTagEqn, bound], good_tag_write good node tag, rfl,
    related.tag_write node tag bound⟩

/-- Concrete Atemp assignment returns the native successful state, preserving
the original invariant and complete production relation. Every neighbour read
and concrete preference result is derived, not supplied. This is untagged
Flapjack actual/native infrastructure, not another HOL assignment port. -/
theorem assignAtempTag_production (limit node : Nat) (table : Spt (List Nat))
    (actualTable : CakeNodeMap (List Nat)) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (tables : ProductionMoveTableRel table actualTable) (bound : node < native.dim) :
    ∃ result,
      assignAtempTag (List.range limit) (biasedPref table) node native = (.success (), result) ∧
      goodRaState result ∧ native.dim = result.dim ∧
      ProductionStateRel result
        (cakeAssignAtempTag limit (fun s n ks => cakeBiasedPref s actualTable n ks) node production) := by
  have tagBound : node < native.node_tag.length := by rwa [good.2.1]
  have adjBound : node < native.adj_ls.length := by rwa [good.1]
  have tagRead := related.tag_read node tagBound
  have adjRead := related.adjacency_read node adjBound
  have neighbours : ∀ next ∈ native.adj_ls[node], next < native.dim := by
    intro next member
    exact good.2.2.2.2.2.2.1 _ (List.getElem_mem adjBound) next member
  have removal := removeColours_production native.adj_ls[node] (List.range limit) related good neighbours
  simp only [assignAtempTag, Translator.Monadic.MonadBase.bind, nodeTagSubEqn,
    if_pos tagBound, holEl_eq_getElem node native.node_tag tagBound,
    cakeAssignAtempTag, tagRead]
  cases native.node_tag[node] with
  | Fixed colour => exact ⟨native, rfl, good, rfl, related⟩
  | Stemp => exact ⟨native, rfl, good, rfl, related⟩
  | Atemp =>
    simp only [Tag.toProduction, Translator.Monadic.MonadBase.bind, adjLsSubEqn, if_pos adjBound,
      holEl_eq_getElem node native.adj_ls adjBound, cakeAdjSub, adjRead,
      Option.getD_some, removal]
    cases colours : cakeRemoveColours production native.adj_ls[node] (List.range limit) with
    | nil => simpa only [colours, Tag.toProduction] using write_production node .Stemp related good tagBound
    | cons first rest =>
      have preference := biasedPref_production table actualTable node (first :: rest) related good tables
      simp only [Translator.Monadic.MonadBase.bind, preference]
      cases chosen : cakeBiasedPref production actualTable node (first :: rest) with
      | none => simpa only [chosen, Tag.toProduction] using write_production node (.Fixed first) related good tagBound
      | some colour => simpa only [chosen, Tag.toProduction] using write_production node (.Fixed colour) related good tagBound

/-- Concrete Stemp assignment derives its forbidden colours and negative
preference, then returns the native state corresponding to the actual write.
This is untagged actual/native infrastructure, not a duplicate HOL port. -/
theorem assignStempTag_production (limit node : Nat) (table : Spt (List Nat))
    (actualTable : CakeNodeMap (List Nat)) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (tables : ProductionMoveTableRel table actualTable) (bound : node < native.dim) :
    ∃ result,
      assignStempTag limit (negBiasedPref limit table) node native = (.success (), result) ∧
      goodRaState result ∧ native.dim = result.dim ∧
      ProductionStateRel result
        (cakeAssignStempTag limit (fun s n bads => cakeNegBiasedPref s limit actualTable n bads) node production) := by
  have tagBound : node < native.node_tag.length := by rwa [good.2.1]
  have adjBound : node < native.adj_ls.length := by rwa [good.1]
  have tagRead := related.tag_read node tagBound
  have adjRead := related.adjacency_read node adjBound
  have neighbours : ∀ next ∈ native.adj_ls[node], next < native.dim :=
    fun next member => good.2.2.2.2.2.2.1 _ (List.getElem_mem adjBound) next member
  obtain ⟨tags, tagRun, colours⟩ := tagMap_production native.adj_ls[node] related good neighbours
  simp only [assignStempTag, Translator.Monadic.MonadBase.bind, nodeTagSubEqn,
    if_pos tagBound, holEl_eq_getElem node native.node_tag tagBound,
    cakeAssignStempTag, tagRead]
  cases native.node_tag[node] with
  | Fixed colour => exact ⟨native, rfl, good, rfl, related⟩
  | Atemp => exact ⟨native, rfl, good, rfl, related⟩
  | Stemp =>
    simp only [Tag.toProduction, Translator.Monadic.MonadBase.bind, adjLsSubEqn,
      if_pos adjBound, holEl_eq_getElem node native.adj_ls adjBound, tagRun,
      colours, cakeAdjSub, adjRead, Option.getD_some, cakeSort_eq_literal]
    let bads := Basis.Pure.MlList.sort (fun x y => decide (x ≤ y))
      (native.adj_ls[node].map (cakeTagCol production))
    have preference := negBiasedPref_production limit table actualTable node bads related tables
    rw [preference]
    cases chosen : cakeNegBiasedPref production limit actualTable node bads with
    | none =>
      simpa only [chosen, Tag.toProduction, cakeUnboundColour] using
        write_production node (.Fixed (unboundColour limit bads)) related good tagBound
    | some colour =>
      simpa only [chosen, Tag.toProduction] using write_production node (.Fixed colour) related good tagBound

private theorem foreach_production
    (action : Nat → M State Unit StateException) (actual : CakeRaState → Nat → CakeRaState)
    (step : ∀ node native production, ProductionStateRel native production → goodRaState native →
      node < native.dim → ∃ result, action node native = (.success (), result) ∧
        goodRaState result ∧ native.dim = result.dim ∧ ProductionStateRel result (actual production node))
    (nodes : List Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bounds : ∀ node ∈ nodes, node < native.dim) :
    ∃ result, stExForeach nodes action native = (.success (), result) ∧
      goodRaState result ∧ native.dim = result.dim ∧
      ProductionStateRel result (nodes.foldl actual production) := by
  induction nodes generalizing native production with
  | nil => exact ⟨native, rfl, good, rfl, related⟩
  | cons node rest ih =>
    obtain ⟨next, run, nextGood, nextDim, nextRel⟩ :=
      step node native production related good (bounds node List.mem_cons_self)
    obtain ⟨result, restRun, resultGood, resultDim, resultRel⟩ :=
      ih nextRel nextGood (fun n member => nextDim ▸ bounds n (List.mem_cons_of_mem node member))
    exact ⟨result, by simp only [stExForeach, ignoreBind, run, restRun], resultGood,
      nextDim.trans resultDim, resultRel⟩

/-- Complete concrete register-colouring pass: the filtered heuristic stack
and subsequent dimension range run in source order, preserving originalGood
and the full state relation. No colour-output premise is assumed. Untagged
actual/native infrastructure rather than a duplicate HOL correctness port. -/
theorem assignAtemps_production (limit : Nat) (nodes : List Nat)
    (table : Spt (List Nat)) (actualTable : CakeNodeMap (List Nat))
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (tables : ProductionMoveTableRel table actualTable) :
    ∃ result, assignAtemps limit nodes (biasedPref table) native = (.success (), result) ∧
      goodRaState result ∧ native.dim = result.dim ∧ ProductionStateRel result
        (cakeAssignAtemps limit nodes (fun s n ks => cakeBiasedPref s actualTable n ks) production) := by
  let action := assignAtempTag (List.range limit) (biasedPref table)
  let actual := fun s n => cakeAssignAtempTag limit (fun s n ks => cakeBiasedPref s actualTable n ks) n s
  have step := fun n s p rel hg hn => assignAtempTag_production limit n table actualTable
    (native := s) (production := p) rel hg tables hn
  let filtered := nodes.filter (fun n => decide (n < native.dim))
  obtain ⟨next, run, nextGood, nextDim, nextRel⟩ := foreach_production action actual step
    filtered related good (fun n member => by simpa [filtered] using (List.mem_filter.mp member).2)
  obtain ⟨result, rangeRun, resultGood, resultDim, resultRel⟩ :=
    foreach_production action actual step (List.range native.dim) nextRel nextGood
      (fun n member => nextDim ▸ List.mem_range.mp member)
  have actualDim : (filtered.foldl actual production).dim = production.dim :=
    nextRel.dimension.trans (nextDim.symm.trans related.dimension.symm)
  refine ⟨result, ?_, resultGood, nextDim.trans resultDim, ?_⟩
  · dsimp only [action] at run rangeRun
    simp only [assignAtemps, Translator.Monadic.MonadBase.bind, getDim, ret,
      ignoreBind, show nodes.filter (fun n => decide (n < native.dim)) = filtered from rfl,
      run, rangeRun]
  · unfold cakeAssignAtemps
    rw [related.dimension]
    change ProductionStateRel result
      ((List.range (filtered.foldl actual production).dim).foldl actual
        (filtered.foldl actual production))
    rw [actualDim, related.dimension]
    exact resultRel

/-- Complete concrete spill-colouring pass over every in-range node, with
derived neighbour reads and native success/state correspondence. This is
untagged actual/native infrastructure. -/
theorem assignStemps_production (limit : Nat) (table : Spt (List Nat))
    (actualTable : CakeNodeMap (List Nat)) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (tables : ProductionMoveTableRel table actualTable) :
    ∃ result, assignStemps limit (negBiasedPref limit table) native = (.success (), result) ∧
      goodRaState result ∧ native.dim = result.dim ∧ ProductionStateRel result
        (cakeAssignStemps limit (fun s n bads => cakeNegBiasedPref s limit actualTable n bads) production) := by
  obtain ⟨result, run, resultGood, resultDim, resultRel⟩ := foreach_production
    (assignStempTag limit (negBiasedPref limit table))
    (fun s n => cakeAssignStempTag limit (fun s n bads => cakeNegBiasedPref s limit actualTable n bads) n s)
    (fun n s p rel hg hn => assignStempTag_production limit n table actualTable rel hg tables hn)
    (List.range native.dim) related good (fun n member => List.mem_range.mp member)
  refine ⟨result, ?_, resultGood, resultDim, ?_⟩
  · simpa only [assignStemps, Translator.Monadic.MonadBase.bind, getDim, ret] using run
  · simpa only [cakeAssignStemps, related.dimension] using resultRel

/-- Complete concrete two-pass colouring slice of cakeDoRegAllocFromState,
including its executed move-table producer. The table relation is constructed
from the original moves; neither a supplied final table nor a target evaluation
is assumed. This proves actual/native state correspondence, not the remaining
graph/bijection initialization or extracted output theorem. -/
theorem colouring_production (dimension limit : Nat) (moves : List (Nat × (Nat × Nat)))
    (nodes : List Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result,
      let table := resortMoves (movesToSp moves .ln)
      let actualTable := cakeResortMovesSp (cakeMovesToSp moves (CakeNodeMap.ofSize dimension))
      ignoreBind (assignAtemps limit nodes (biasedPref table))
        (assignStemps limit (negBiasedPref limit table)) native = (.success (), result) ∧
      goodRaState result ∧ native.dim = result.dim ∧ ProductionStateRel result
        (cakeAssignStemps limit (fun s n bads => cakeNegBiasedPref s limit actualTable n bads)
          (cakeAssignAtemps limit nodes (fun s n ks => cakeBiasedPref s actualTable n ks) production)) := by
  let table := resortMoves (movesToSp moves .ln)
  let actualTable := cakeResortMovesSp (cakeMovesToSp moves (CakeNodeMap.ofSize dimension))
  have tables := preferenceTable_production dimension moves
  obtain ⟨next, run, nextGood, nextDim, nextRel⟩ :=
    assignAtemps_production limit nodes table actualTable related good tables
  obtain ⟨result, spillRun, resultGood, resultDim, resultRel⟩ :=
    assignStemps_production limit table actualTable nextRel nextGood tables
  dsimp only [table] at run spillRun
  exact ⟨result, by simp only [ignoreBind, run, spillRun], resultGood,
    nextDim.trans resultDim, resultRel⟩

end Flapjack.RegAlloc
