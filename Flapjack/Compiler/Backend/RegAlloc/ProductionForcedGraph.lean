import Flapjack.Compiler.Backend.RegAlloc.ProductionCliqueBatch

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc

/-- Actual forced-edge traversal and native monadic traversal update every
state field in lockstep. Endpoint bounds refer to the original incoming
state and are propagated by proved length preservation. Untagged actual/native
infrastructure; extendGraph already has its reviewed HOL definition tag. -/
theorem extendGraphReference_production (ta : Nat → Nat) (forced : List (Nat × Nat))
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production)
    (bounds : ∀ pair ∈ forced,
      ta pair.1 < native.adj_ls.length ∧ ta pair.2 < native.adj_ls.length) :
    ∃ result, extendGraph ta forced native = (.success (), result) ∧
      result.adj_ls.length = native.adj_ls.length ∧
      ProductionStateRel result {production with
        adjLists := cakeExtendGraph ta forced production.adjLists
        adjSets := production.adjSets.map (cakeExtendGraphSet ta forced)} := by
  induction forced generalizing native production with
  | nil =>
    refine ⟨native, rfl, rfl, ?_⟩
    have identity : production.adjSets.map (fun cache => cache) = production.adjSets := by
      cases production.adjSets <;> rfl
    simpa only [cakeExtendGraph, cakeExtendGraphSet, identity] using related
  | cons pair rest ih =>
    rcases pair with ⟨x, y⟩
    have endpointBounds := bounds (x, y) List.mem_cons_self
    obtain ⟨first, firstRun, firstLength, firstRel⟩ := insertEdge_production (ta x) (ta y)
      related endpointBounds.1 endpointBounds.2
    obtain ⟨result, run, length, rel⟩ := ih firstRel (by
      intro pair belongs
      rw [firstLength]
      exact bounds pair (List.mem_cons_of_mem _ belongs))
    refine ⟨result, ?_, length.trans firstLength, ?_⟩
    · simp only [extendGraph, Translator.Monadic.MonadBase.ignoreBind, firstRun, run]
    · simpa only [cakeExtendGraph, cakeExtendGraphSet, Option.map_map,
        Function.comp_def] using rel

/-- Exact full-map materialization for the real forced-edge cache traversal.
This unconditional equation covers equal endpoints, repeated pairs, missing
rows and outside keys, as well as the descending row order. Untagged codec
infrastructure for the actual graph producer, not a new HOL definition. -/
theorem extendGraphSet_materialize (ta : Nat → Nat) (forced : List (Nat × Nat))
    (cache : CakeNodeMap (Std.TreeSet Nat)) :
    (cakeExtendGraphSet ta forced cache).mapValues cakeAdjSetList =
      cakeExtendGraph ta forced (cache.mapValues cakeAdjSetList) := by
  induction forced generalizing cache with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨x, y⟩
    rw [cakeExtendGraphSet, ih, cakeInsertEdgeSet_materialize_eq]
    rfl

/-- Full native correspondence for the cache-only forced graph operation
the executed initializer actually calls. Original endpoint bounds supply the
read/write domain; materialized rows and every resulting native state field
are conclusions. This is untagged actual/native correspondence. -/
theorem extendGraphSet_production (ta : Nat → Nat) (forced : List (Nat × Nat))
    (cache : CakeNodeMap (Std.TreeSet Nat)) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native {production with
      adjLists := cache.mapValues cakeAdjSetList, adjSets := some cache})
    (bounds : ∀ pair ∈ forced,
      ta pair.1 < native.adj_ls.length ∧ ta pair.2 < native.adj_ls.length) :
    ∃ result, extendGraph ta forced native = (.success (), result) ∧
      result.adj_ls.length = native.adj_ls.length ∧
      ProductionStateRel result {production with
        adjLists := (cakeExtendGraphSet ta forced cache).mapValues cakeAdjSetList
        adjSets := some (cakeExtendGraphSet ta forced cache)} := by
  obtain ⟨result, run, length, rel⟩ := extendGraphReference_production ta forced related bounds
  refine ⟨result, run, length, ?_⟩
  simpa only [extendGraphSet_materialize, Option.map_some] using rel

end Flapjack.RegAlloc
