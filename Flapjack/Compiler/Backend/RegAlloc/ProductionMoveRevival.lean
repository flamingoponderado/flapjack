import Flapjack.Compiler.Backend.RegAlloc.ProductionAdjacencyQuery
import Flapjack.Compiler.Backend.RegAlloc.Proofs.PhaseSuccess

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

private theorem holPart_filter_reverse {α : Type} (predicate : α → Bool)
    (nodes yes no : List α) :
    holPart predicate nodes yes no =
      ((nodes.filter predicate).reverse ++ yes,
        (nodes.filter (fun node => !predicate node)).reverse ++ no) := by
  induction nodes generalizing yes no with
  | nil => simp [holPart]
  | cons node rest ih =>
    cases choice : predicate node <;>
      simp [holPart, choice, ih, List.reverse_cons, List.append_assoc]

/-- Actual reversed partition is the native sorting PARTITION for every
predicate and list. This codec equation is Flapjack infrastructure, with no
independent HOL declaration; the native definition already has its own tag. -/
theorem partitionReversed_production {α : Type} (predicate : α → Bool) (nodes : List α) :
    partitionReversed predicate nodes = holPartition predicate nodes := by
  simp [partitionReversed, holPartition, holPart_filter_reverse, Function.comp_def]

private theorem adjacency_any_production (neighbour : Nat) (nodes : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bounds : ∀ node ∈ nodes, node < native.dim) :
    (nodes.map (fun node => holEl node native.adj_ls)).any
        (fun row => sortedMem neighbour row) =
      nodes.any (fun node => cakeAdjMem production neighbour node) := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    simp only [List.map_cons, List.any_cons]
    rw [cakeAdjMem_production neighbour node related good (bounds node List.mem_cons_self)]
    rw [ih (fun next member => bounds next (List.mem_cons_of_mem node member))]

/-- The complete executed move-revival transition agrees with the native
monad on the original good state and EVERY-node bound. Native MAP reads,
partition order, sort/merge and the full post-state relation are derived.
This is actual/native correspondence infrastructure, not a duplicate port of
revive_moves_success. It makes no claim about malformed adjacency states. -/
theorem reviveMoves_production (nodes : List Nat) {native : State}
    {production : CakeRaState} (related : ProductionStateRel native production)
    (good : goodRaState native) (bounds : ∀ node ∈ nodes, node < native.dim) :
    ∃ result : State, reviveMoves nodes native = (.success (), result) ∧
      ProductionStateRel result (cakeReviveMoves nodes production) := by
  let predicate := fun (move : Nat × (Nat × Nat)) =>
    (nodes.map (fun node => holEl node native.adj_ls)).any
        (fun row => sortedMem move.2.1 row) ||
      (nodes.map (fun node => holEl node native.adj_ls)).any
        (fun row => sortedMem move.2.2 row)
  let parts := holPartition predicate native.unavail_moves_wl
  let available := smerge (sortMoves parts.1) native.avail_moves_wl
  let result : State := {native with
    avail_moves_wl := available
    unavail_moves_wl := parts.2}
  have reads := stExMapAdjLsSub nodes native (by
    intro node member
    simpa only [good.1] using bounds node member)
  have source : reviveMoves nodes native = (.success (), result) := by
    simp only [reviveMoves, Translator.Monadic.MonadBase.bind, reads,
      getUnavailMovesWl, getAvailMovesWl, ignoreBind, setAvailMovesWl, setUnavailMovesWl]
    rfl
  have predicates : (fun (move : Nat × (Nat × Nat)) =>
      nodes.any (fun node => cakeAdjMem production move.2.1 node) ||
        nodes.any (fun node => cakeAdjMem production move.2.2 node)) = predicate := by
    funext move
    dsimp [predicate]
    rw [adjacency_any_production move.2.1 nodes related good bounds,
      adjacency_any_production move.2.2 nodes related good bounds]
  have actual : cakeReviveMoves nodes production = {production with
      availMovesWl := available
      unavailMovesWl := parts.2} := by
    unfold cakeReviveMoves
    rw [predicates, related.unavailableMoves, partitionReversed_production]
    simp only [cakeSMerge, cakeSortMoves, related.availableMoves]
    rfl
  refine ⟨result, source, ?_⟩
  rw [actual]
  exact {related with availableMoves := rfl, unavailableMoves := rfl}

end Flapjack.RegAlloc
