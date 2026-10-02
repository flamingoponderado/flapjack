import Flapjack.Compiler.Backend.RegAlloc.ProductionDegreeTransition

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- Further actual degree updates preserve the first latched failure. -/
private theorem degreeFold_latched (nodes : List Nat) (production : CakeRaState)
    (error : CakeRaFailure) (failed : production.failure = some error) :
    nodes.foldl (fun state node => cakeDecDeg node state) production = production := by
  induction nodes generalizing production with
  | nil => rfl
  | cons node rest ih =>
      simp only [List.foldl_cons]
      have unchanged : cakeDecDeg node production = production := by
        simp [cakeDecDeg, failed]
      rw [unchanged]
      exact ih production failed

/-- Actual head-to-tail degree traversal has the complete native FOREACH
result/state, including the first failure and skipped remaining actions.
No successful traversal, degree bound, or desired post-state is assumed. -/
theorem degreeForeach_production (nodes : List Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) :
    ProductionLatchedUnitRel (stExForeach nodes decDeg native)
      (nodes.foldl (fun state node => cakeDecDeg node state) production) := by
  induction nodes generalizing native production with
  | nil => simpa [stExForeach, ret, ProductionLatchedUnitRel] using related
  | cons node rest ih =>
      have step := decDeg_production_latched node related
      simp only [stExForeach, List.foldl_cons, ignoreBind]
      generalize hn : decDeg node native = result at step ⊢
      rcases result with ⟨value, final⟩
      cases value with
      | success value =>
          cases value
          simp only [ProductionLatchedUnitRel] at step
          exact ih step
      | failure error =>
          cases error with
          | Fail message => simp [ProductionLatchedUnitRel] at step
          | Subscript =>
              simp only [ProductionLatchedUnitRel] at step
              rw [degreeFold_latched rest _ .subscript step.1]
              exact step

/-- A represented list has no binding at any out-of-list key, including
extension-map keys. This distinguishes Subscript from a fabricated empty row. -/
private theorem represented_get_none {α : Type}
    (production : CakeNodeMap α) (native : List α)
    (related : CakeNodeMap.RepresentsHOLNodeList production native)
    (node : Nat) (bound : ¬ node < native.length) : production.get node = none := by
  have outside : ¬ node < production.slots.size := by rwa [related.2.1]
  simp [CakeNodeMap.get, outside, related.1, cakeMapLookup, lookupNatInfo]

/-- The actual repaired neighbour traversal agrees with complete native
`decDegree` at every index and every represented native state, including an
in-dimension node whose adjacency list is too short. The source Subscript is
preserved in the pipeline latch, rather than narrowed away by a bound premise.
This cross-implementation theorem has no separate HOL original. -/
theorem decDegree_production (node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) :
    ProductionLatchedUnitRel (decDegree node native) (cakeDecDegree node production) := by
  by_cases dimension : node < native.dim
  · by_cases bound : node < native.adj_ls.length
    · have row := related.adjacency_read node bound
      have source : decDegree node native = stExForeach native.adj_ls[node] decDeg native := by
        simp [decDegree, Translator.Monadic.MonadBase.bind, getDim,
          dimension, adjLsSubEqn, bound, holEl_eq_getElem node native.adj_ls bound]
      have actual : cakeDecDegree node production =
          native.adj_ls[node].foldl (fun state node => cakeDecDeg node state) production := by
        simp [cakeDecDegree, related.failure, related.dimension, dimension, row]
      rw [source, actual]
      exact degreeForeach_production _ related
    · have row := represented_get_none _ _ related.adjacency node bound
      have source : decDegree node native = (.failure .Subscript, native) := by
        simp [decDegree, Translator.Monadic.MonadBase.bind, getDim,
          dimension, adjLsSubEqn, bound]
      have cleared : {production with failure := none} = production := by
        rw [← related.failure]
      have actual : cakeDecDegree node production = {production with failure := some .subscript} := by
        simp [cakeDecDegree, related.failure, related.dimension, dimension, row]
      simpa only [source, actual, ProductionLatchedUnitRel, cleared] using
        (And.intro rfl related :
          (some CakeRaFailure.subscript : Option CakeRaFailure) = some .subscript ∧
            ProductionStateRel native production)
  · have source : decDegree node native = (.success (), native) := by
      simp [decDegree, Translator.Monadic.MonadBase.bind, getDim, dimension, ret]
    simpa [source, ProductionLatchedUnitRel, cakeDecDegree,
      related.failure, related.dimension, dimension] using related

end Flapjack.RegAlloc
