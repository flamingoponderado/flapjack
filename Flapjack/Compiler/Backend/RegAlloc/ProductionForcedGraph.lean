import Flapjack.Compiler.Backend.RegAlloc.ProductionEdgeUpdate

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

end Flapjack.RegAlloc
