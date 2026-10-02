import Flapjack.Compiler.Backend.RegAlloc.ProductionColourReads
import Flapjack.Compiler.Backend.RegAlloc.StempColouring

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

private theorem tagMap_production (nodes : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bounds : ∀ node ∈ nodes, node < native.dim) :
    ∃ tags, stExMap nodeTagSub nodes native = (.success tags, native) ∧
      tags.map tagCol = nodes.map (cakeTagCol production) := by
  induction nodes with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons node rest ih =>
    have bound : node < native.node_tag.length := by
      rw [good.2.1]
      exact bounds node List.mem_cons_self
    have read := related.tag_read node bound
    obtain ⟨tags, run, colours⟩ := ih
      (fun next member => bounds next (List.mem_cons_of_mem node member))
    refine ⟨native.node_tag[node] :: tags, ?_, ?_⟩
    · simp only [stExMap, Translator.Monadic.MonadBase.bind, nodeTagSubEqn,
        if_pos bound, holEl_eq_getElem node native.node_tag bound, run, ret]
    · simp only [List.map_cons, colours, cakeTagCol, read]
      cases native.node_tag[node] <;> rfl

/-- Complete native tag-map and sorted forbidden-colour query agrees with
the executed Stemp phase's map/sort. Bounds derive all native reads; the actual
generic sort is proved equal to the reviewed library sort for arbitrary inputs.
This is implementation correspondence, not a separate HOL declaration port. -/
theorem sortedColourMap_production (nodes : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bounds : ∀ node ∈ nodes, node < native.dim) :
    bind (stExMap nodeTagSub nodes) (fun tags =>
      ret (Basis.Pure.MlList.sort (fun x y => decide (x ≤ y)) (tags.map tagCol))) native =
      (.success (cakeSort (fun x y => x ≤ y) (nodes.map (cakeTagCol production))), native) := by
  obtain ⟨tags, run, colours⟩ := tagMap_production nodes related good bounds
  simp only [Translator.Monadic.MonadBase.bind, run, ret, colours, cakeSort_eq_literal]

/-- Full negative first-match colour query preserves list order and native
state. All tag domains derive from the original invariant and input bounds;
Nat membership and the lower-limit comparison agree in both implementations.
This is actual/native infrastructure without an independent HOL original. -/
theorem negFirstMatchCol_production (limit : Nat) (bads nodes : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bounds : ∀ node ∈ nodes, node < native.dim) :
    negFirstMatchCol limit bads nodes native =
      (.success (cakeNegFirstMatchCol production limit bads nodes), native) := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    have bound : node < native.node_tag.length := by
      rw [good.2.1]
      exact bounds node List.mem_cons_self
    have read := related.tag_read node bound
    have tailBounds : ∀ next ∈ rest, next < native.dim :=
      fun next member => bounds next (List.mem_cons_of_mem node member)
    simp only [negFirstMatchCol, Translator.Monadic.MonadBase.bind, nodeTagSubEqn,
      if_pos bound, holEl_eq_getElem node native.node_tag bound,
      cakeNegFirstMatchCol, read]
    cases native.node_tag[node] <;> simp only [Tag.toProduction, ih tailBounds]
    all_goals first | rfl | (split <;> simp_all [ret] <;> omega)

end Flapjack.RegAlloc
