import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace Flapjack.PanSimp

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Flapjack-specific representation witness: HOL has no separate codec
roundtrip theorem. The canonical carrier owns the code map used below. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- HOL's code-only state relation, retaining both absent and successful
lookups. Names, parameter shapes, bodies and return shapes use exact carriers;
only the canonical finite-map and positive word-width translations apply. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "state_rel_def"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.code, c])
  (words_as_type_indexed_bitvec)]
def stateRel {width : Nat} {σ : Type} [NeZero width]
    (s t : PanSemStateFiniteExact width σ)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) : Prop :=
  t = { s with code := c } ∧
  (∀ f, s.code.lookup f = none → c.lookup f = none) ∧
  (∀ f vshs prog rshape,
    s.code.lookup f = some (vshs, prog, rshape) →
    c.lookup f = some (vshs, panSimpCompileHOL prog, rshape))

/-- HOL's introduction projection retains the state update and successful
lookup conjunct, with no evaluation or simulation premise added. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "state_rel_intro"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.code, c])
  (words_as_type_indexed_bitvec)]
theorem stateRel_intro {width : Nat} {σ : Type} [NeZero width]
    (s t : PanSemStateFiniteExact width σ)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    stateRel s t c →
      t = { s with code := c } ∧
      (∀ f vshs prog rshape,
        s.code.lookup f = some (vshs, prog, rshape) →
        c.lookup f = some (vshs, panSimpCompileHOL prog, rshape)) := by
  intro h
  exact ⟨h.1, h.2.2⟩

end Flapjack.PanSimp
