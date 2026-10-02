import Flapjack.Compiler.Backend.RegAlloc.ProductionAdjacencyCache
import Flapjack.Compiler.Backend.RegAlloc.Proofs.EdgeInsertion

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc

/-- The actual optimized query agrees with native early-exit sorted_mem on
an original good allocator state. The row bound and sorting are derived from
that invariant; both cached and uncached production paths are covered. A cache
entry is derived from the complete representation, not assumed as an extra
successful lookup. This cross-implementation equation has no HOL original.
It does not assert equivalence on unsorted or malformed states. -/
theorem cakeAdjMem_production (neighbour node : Nat) {native : State}
    {production : CakeRaState} (related : ProductionStateRel native production)
    (good : goodRaState native) (bound : node < native.dim) :
    cakeAdjMem production neighbour node = sortedMem neighbour (holEl node native.adj_ls) := by
  have rowBound : node < native.adj_ls.length := by rwa [good.1]
  have row := related.adjacency_read node rowBound
  have sorted : holSorted (· > ·) native.adj_ls[node] :=
    good.2.2.2.2.2.2.2.1 _ (List.getElem_mem rowBound)
  have source : sortedMem neighbour native.adj_ls[node] =
      decide (neighbour ∈ native.adj_ls[node]) := by
    have membership := sortedMemCorrect neighbour _ sorted
    cases value : sortedMem neighbour native.adj_ls[node] <;>
      simp_all
  rw [holEl_eq_getElem node native.adj_ls rowBound, source]
  cases cache : production.adjSets with
  | none => simp [cakeAdjMem, cache, cakeAdjSub, row, cakeSortedMem, source]
  | some entries =>
    have sound := related.adjacencyCache
    simp only [ProductionAdjacencyCacheSound, cache] at sound
    have membership := sound node neighbour
    rw [row] at membership
    cases lookup : entries.get node with
    | none => simp [lookup] at membership
    | some neighbours =>
      simp only [lookup, Option.map_some, Option.some.injEq] at membership
      simpa [cakeAdjMem, cache, lookup] using membership

end Flapjack.RegAlloc
