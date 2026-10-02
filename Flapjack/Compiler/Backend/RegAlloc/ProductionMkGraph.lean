import Flapjack.Compiler.Backend.RegAlloc.ProductionForcedGraph

namespace Flapjack.RegAlloc
open RiscV RiscV.CakeRegAlloc

/-- Original input-node domain for the executed graph traversal. Set clauses
use the actual mixed-order enumeration, whose native codec is already proved.
This Flapjack predicate does not assume a graph output or native evaluation;
the initializer must discharge it from its real bijection bounds. -/
def ProductionGraphInputBound (ta : Nat → Nat) (dimension : Nat) : WordClashTree → Prop
  | .delta writes reads =>
      (∀ node ∈ writes, ta node < dimension) ∧ (∀ node ∈ reads, ta node < dimension)
  | .set names => ∀ node ∈ NumSet.fromAList names, ta node < dimension
  | .branch live left right =>
      ProductionGraphInputBound ta dimension left ∧ ProductionGraphInputBound ta dimension right ∧
        (∀ names, live = some names → ∀ node ∈ NumSet.fromAList names, ta node < dimension)
  | .seq left right => ProductionGraphInputBound ta dimension left ∧ ProductionGraphInputBound ta dimension right

/-- Admission preserves bounds derived solely from its original two input
lists. Untagged actual traversal infrastructure; no returned live list is
provided as a premise. -/
theorem cliqueAdmission_bound (new initial : List Nat) (dimension : Nat)
    (newBound : ∀ node ∈ new, node < dimension)
    (initialBound : ∀ node ∈ initial, node < dimension) :
    ∀ node ∈ cliqueAdmission new initial, node < dimension := by
  induction new generalizing initial with
  | nil => exact initialBound
  | cons node rest ih =>
    simp only [cliqueAdmission]
    split
    · exact ih initial (fun next belongs => newBound next (List.mem_cons_of_mem _ belongs)) initialBound
    · apply ih (node :: initial) (fun next belongs => newBound next (List.mem_cons_of_mem _ belongs))
      intro next belongs
      rcases List.mem_cons.mp belongs with rfl | belongs
      · exact newBound _ List.mem_cons_self
      · exact initialBound next belongs

/-- The executed batch caller returns a bounded live list from bounded
original input lists. The graph cache supplies no additional premise. -/
theorem extendCliqueSet_live_bound (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) (dimension : Nat)
    (newBound : ∀ node ∈ new, node < dimension)
    (initialBound : ∀ node ∈ initial, node < dimension) :
    ∀ node ∈ (cakeExtendCliqueSet new initial cache).2, node < dimension := by
  simpa only [cakeExtendCliqueSet, cakeExtendCliqueSetFast, extendCliqueBatch_live] using
    cliqueAdmission_bound new initial dimension newBound initialBound

/-- Every returned live node of the complete executed graph traversal is
bounded by the original input dimension. This proves the intermediate domains
needed by Branch and Seq composition; it assumes neither graph output nor
success. Untagged actual producer infrastructure. -/
theorem mkGraphSet_live_bound (ta : Nat → Nat) (dimension : Nat) (tree : WordClashTree)
    (liveout : List Nat) (cache : CakeNodeMap (Std.TreeSet Nat))
    (inputBound : ProductionGraphInputBound ta dimension tree)
    (liveBound : ∀ node ∈ liveout, node < dimension) :
    ∀ node ∈ (cakeMkGraphSet ta tree liveout cache).2, node < dimension := by
  induction tree generalizing liveout cache with
  | delta writes reads =>
    rw [cakeMkGraphSet]
    have writeBound : ∀ node ∈ writes.map ta, node < dimension := by
      intro node belongs
      obtain ⟨name, sourceMember, rfl⟩ := List.mem_map.mp belongs
      exact inputBound.1 name sourceMember
    have readBound : ∀ node ∈ reads.map ta, node < dimension := by
      intro node belongs
      obtain ⟨name, sourceMember, rfl⟩ := List.mem_map.mp belongs
      exact inputBound.2 name sourceMember
    have first := extendCliqueSet_live_bound (writes.map ta) liveout cache dimension writeBound liveBound
    apply extendCliqueSet_live_bound (reads.map ta) _ _ dimension readBound
    intro node belongs
    exact first node ((List.mem_filter.mp belongs).1)
  | set names =>
    rw [cakeMkGraphSet]
    intro node belongs
    change node ∈ (NumSet.fromAList names).map ta at belongs
    obtain ⟨name, sourceMember, rfl⟩ := List.mem_map.mp belongs
    exact inputBound name sourceMember
  | branch live left right ihLeft ihRight =>
    have first := ihLeft liveout cache inputBound.1 liveBound
    have second := ihRight liveout (cakeMkGraphSet ta left liveout cache).1 inputBound.2.1 liveBound
    cases live with
    | none =>
      rw [cakeMkGraphSet]
      exact extendCliqueSet_live_bound _ _ _ dimension first second
    | some names =>
      rw [cakeMkGraphSet]
      intro node belongs
      change node ∈ (NumSet.fromAList names).map ta at belongs
      obtain ⟨name, sourceMember, rfl⟩ := List.mem_map.mp belongs
      exact inputBound.2.2 names rfl name sourceMember
  | seq left right ihLeft ihRight =>
    rw [cakeMkGraphSet]
    have second := ihRight liveout cache inputBound.2 liveBound
    exact ihLeft _ _ inputBound.1 second

private theorem graphSetKeys (names : List Nat) :
    (sptToAList (sptFromAList (names.map (fun name => (name, ()))))).map Prod.fst =
      NumSet.fromAList names := by
  have keys := congrArg (List.map Prod.fst) (numSetFromAList_production names)
  simpa [List.map_map, Function.comp_def] using keys.symm

/-- Complete executed cached graph traversal/native evaluation correspondence
on the canonical input codec. Original input-tree and incoming-live bounds
derive every intermediate domain. The returned live list, successful native
evaluation and full resulting state are conclusions, not premises.
Untagged cross-implementation infrastructure; native mkGraph is already tagged.
Original WordAlloc producer linkage remains a separate obligation. -/
theorem mkGraphSet_production (ta : Nat → Nat) (tree : WordClashTree) (liveout : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native {production with
      adjLists := cache.mapValues cakeAdjSetList, adjSets := some cache})
    (inputBound : ProductionGraphInputBound ta native.adj_ls.length tree)
    (liveBound : ∀ node ∈ liveout, node < native.adj_ls.length) :
    ∃ result, mkGraph ta (productionClashTreeToNative tree) liveout native =
        (.success (cakeMkGraphSet ta tree liveout cache).2, result) ∧
      result.adj_ls.length = native.adj_ls.length ∧
      ProductionStateRel result {production with
        adjLists := (cakeMkGraphSet ta tree liveout cache).1.mapValues cakeAdjSetList
        adjSets := some (cakeMkGraphSet ta tree liveout cache).1} := by
  induction tree generalizing native production liveout cache with
  | delta writes reads =>
    have writeBound : ∀ node ∈ writes.map ta, node < native.adj_ls.length := by
      intro node belongs
      obtain ⟨name, sourceMember, rfl⟩ := List.mem_map.mp belongs
      exact inputBound.1 name sourceMember
    obtain ⟨first, firstRun, firstLength, firstRel⟩ := extendCliqueSet_production
      (writes.map ta) liveout cache related (by
        intro node belongs
        exact belongs.elim (writeBound node) (liveBound node))
    have firstLive := extendCliqueSet_live_bound (writes.map ta) liveout cache
      native.adj_ls.length writeBound liveBound
    obtain ⟨result, run, length, rel⟩ := extendCliqueSet_production
      (reads.map ta) ((cakeExtendCliqueSet (writes.map ta) liveout cache).2.filter
        (fun node => !(writes.map ta).contains node))
      (cakeExtendCliqueSet (writes.map ta) liveout cache).1 firstRel (by
        intro node belongs
        rw [firstLength]
        rcases belongs with belongs | belongs
        · obtain ⟨name, sourceMember, rfl⟩ := List.mem_map.mp belongs
          exact inputBound.2 name sourceMember
        · exact firstLive node (List.mem_filter.mp belongs).1)
    have filterEq : (cakeExtendCliqueSet (writes.map ta) liveout cache).2.filter
        (fun node => decide (node ∉ writes.map ta)) =
        (cakeExtendCliqueSet (writes.map ta) liveout cache).2.filter
          (fun node => !(writes.map ta).contains node) := by
      apply congrArg (fun predicate => List.filter predicate
        (cakeExtendCliqueSet (writes.map ta) liveout cache).2)
      funext node
      rw [List.contains_eq_mem]
      by_cases belongs : node ∈ writes.map ta <;> simp [belongs]
    refine ⟨result, ?_, length.trans firstLength, ?_⟩
    · simp only [productionClashTreeToNative, mkGraph,
        Translator.Monadic.MonadBase.bind, Translator.Monadic.MonadBase.ret,
        firstRun, filterEq, run, cakeMkGraphSet]
    · simpa only [cakeMkGraphSet] using rel
  | set names =>
    obtain ⟨result, run, length, rel⟩ := cliqueInsertEdgeFast_production
      ((NumSet.fromAList names).map ta) cache related (by
        intro node belongs
        obtain ⟨name, sourceMember, rfl⟩ := List.mem_map.mp belongs
        exact inputBound name sourceMember)
    refine ⟨result, ?_, length, ?_⟩
    · simp only [productionClashTreeToNative, mkGraph, graphSetKeys,
        Translator.Monadic.MonadBase.bind, Translator.Monadic.MonadBase.ret,
        Translator.Monadic.MonadBase.ignoreBind, run, cakeMkGraphSet]
    · simpa only [cakeMkGraphSet] using rel
  | branch live left right ihLeft ihRight =>
    obtain ⟨first, firstRun, firstLength, firstRel⟩ := ihLeft liveout cache related inputBound.1 liveBound
    obtain ⟨second, secondRun, secondLength, secondRel⟩ := ihRight liveout
      (cakeMkGraphSet ta left liveout cache).1 firstRel
      (by simpa only [firstLength] using inputBound.2.1)
      (by simpa only [firstLength] using liveBound)
    cases live with
    | none =>
      have leftLive := mkGraphSet_live_bound ta native.adj_ls.length left liveout cache inputBound.1 liveBound
      have rightLive := mkGraphSet_live_bound ta native.adj_ls.length right liveout
        (cakeMkGraphSet ta left liveout cache).1 inputBound.2.1 liveBound
      obtain ⟨result, run, length, rel⟩ := extendCliqueSet_production
        (cakeMkGraphSet ta left liveout cache).2
        (cakeMkGraphSet ta right liveout (cakeMkGraphSet ta left liveout cache).1).2
        (cakeMkGraphSet ta right liveout (cakeMkGraphSet ta left liveout cache).1).1
        secondRel (by
          intro node belongs
          rw [secondLength, firstLength]
          exact belongs.elim (leftLive node) (rightLive node))
      refine ⟨result, ?_, (length.trans secondLength).trans firstLength, ?_⟩
      · simp only [productionClashTreeToNative, mkGraph, Option.map_none,
          Translator.Monadic.MonadBase.bind, Translator.Monadic.MonadBase.ret,
          firstRun, secondRun, run, cakeMkGraphSet]
      · simpa only [cakeMkGraphSet] using rel
    | some names =>
      obtain ⟨result, run, length, rel⟩ := cliqueInsertEdgeFast_production
        ((NumSet.fromAList names).map ta)
        (cakeMkGraphSet ta right liveout (cakeMkGraphSet ta left liveout cache).1).1
        secondRel (by
          intro node belongs
          rw [secondLength, firstLength]
          obtain ⟨name, sourceMember, rfl⟩ := List.mem_map.mp belongs
          exact inputBound.2.2 names rfl name sourceMember)
      refine ⟨result, ?_, (length.trans secondLength).trans firstLength, ?_⟩
      · simp only [productionClashTreeToNative, mkGraph, Option.map_some, graphSetKeys,
          Translator.Monadic.MonadBase.bind, Translator.Monadic.MonadBase.ret,
          Translator.Monadic.MonadBase.ignoreBind, firstRun, secondRun, run, cakeMkGraphSet]
      · simpa only [cakeMkGraphSet] using rel
  | seq left right ihLeft ihRight =>
    obtain ⟨first, firstRun, firstLength, firstRel⟩ := ihRight liveout cache related inputBound.2 liveBound
    have firstLive := mkGraphSet_live_bound ta native.adj_ls.length right liveout cache inputBound.2 liveBound
    obtain ⟨result, run, length, rel⟩ := ihLeft (cakeMkGraphSet ta right liveout cache).2
      (cakeMkGraphSet ta right liveout cache).1 firstRel
      (by simpa only [firstLength] using inputBound.1)
      (by simpa only [firstLength] using firstLive)
    refine ⟨result, ?_, length.trans firstLength, ?_⟩
    · simp only [productionClashTreeToNative, mkGraph, Translator.Monadic.MonadBase.bind,
        firstRun, run, cakeMkGraphSet]
    · simpa only [cakeMkGraphSet] using rel

/-- Source-routed variant for an original well-formed native clash tree.
The checked codec roundtrip proves that the evaluator here uses that original
tree, rather than merely a canonical replacement. Its real producer must still
supply set well-formedness and input bounds; no output relation is a premise.
Untagged actual/native producer infrastructure. -/
theorem mkGraphSet_original_production (ta : Nat → Nat) (tree : ClashTree)
    (wellFormed : NativeClashTreeSetsWf tree) (liveout : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native {production with
      adjLists := cache.mapValues cakeAdjSetList, adjSets := some cache})
    (inputBound : ProductionGraphInputBound ta native.adj_ls.length (nativeClashTreeToProduction tree))
    (liveBound : ∀ node ∈ liveout, node < native.adj_ls.length) :
    ∃ result, mkGraph ta tree liveout native =
        (.success (cakeMkGraphSet ta (nativeClashTreeToProduction tree) liveout cache).2, result) ∧
      result.adj_ls.length = native.adj_ls.length ∧
      ProductionStateRel result {production with
        adjLists := (cakeMkGraphSet ta (nativeClashTreeToProduction tree) liveout cache).1.mapValues cakeAdjSetList
        adjSets := some (cakeMkGraphSet ta (nativeClashTreeToProduction tree) liveout cache).1} := by
  simpa only [clashTreeCodec_roundtrip tree wellFormed] using
    mkGraphSet_production ta (nativeClashTreeToProduction tree) liveout cache related inputBound liveBound

end Flapjack.RegAlloc
