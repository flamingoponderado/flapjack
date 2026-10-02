import Flapjack.Compiler.Backend.RegAlloc.ProductionAllocLoop
import Flapjack.Compiler.Backend.RegAlloc.Colouring

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

private theorem removeColours_empty (production : CakeRaState) (nodes : List Nat) :
    cakeRemoveColours production nodes [] = [] := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    simp only [cakeRemoveColours]
    cases read : production.nodeTag.get node with
    | none => exact ih
    | some tag => cases tag <;> simpa only [List.filter_nil] using ih

/-- Full colour-removal correspondence. The native empty-colour clause stops
before reading a node; the actual recursion still returns the same empty
list. All nonempty tag reads follow from the original bounds and representation.
This relates the actual implementation to the existing native HOL port. -/
theorem removeColours_production (nodes colours : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bounds : ∀ node ∈ nodes, node < native.dim) :
    removeColours nodes colours native =
      (.success (cakeRemoveColours production nodes colours), native) := by
  induction nodes generalizing colours with
  | nil => cases colours <;> rfl
  | cons node rest ih =>
    cases colours with
    | nil => rw [removeColours_empty]; rfl
    | cons colour colours =>
      have bound : node < native.node_tag.length := by
        rw [good.2.1]
        exact bounds node List.mem_cons_self
      have read := related.tag_read node bound
      have tailBounds : ∀ next ∈ rest, next < native.dim :=
        fun next member => bounds next (List.mem_cons_of_mem node member)
      simp only [removeColours, Translator.Monadic.MonadBase.bind, nodeTagSubEqn,
        if_pos bound, holEl_eq_getElem node native.node_tag bound,
        cakeRemoveColours, read]
      cases native.node_tag[node] <;>
        simp only [Tag.toProduction, ih _ tailBounds, ret]

/-- Complete first matching fixed-colour query correspondence, preserving
node order, first-match selection and unchanged state. Original bounds derive
every tag read; Nat membership uses the same equality in both implementations.
This is actual/native infrastructure, not another first_match_col HOL port. -/
theorem firstMatchCol_production (colours nodes : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bounds : ∀ node ∈ nodes, node < native.dim) :
    firstMatchCol colours nodes native =
      (.success (cakeFirstMatchCol production colours nodes), native) := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    have bound : node < native.node_tag.length := by
      rw [good.2.1]
      exact bounds node List.mem_cons_self
    have read := related.tag_read node bound
    have tailBounds : ∀ next ∈ rest, next < native.dim :=
      fun next member => bounds next (List.mem_cons_of_mem node member)
    simp only [firstMatchCol, Translator.Monadic.MonadBase.bind, nodeTagSubEqn,
      if_pos bound, holEl_eq_getElem node native.node_tag bound,
      cakeFirstMatchCol, read]
    cases native.node_tag[node] <;> simp only [Tag.toProduction, ih tailBounds]
    all_goals first | rfl | (split <;> simp_all [ret])

end Flapjack.RegAlloc
