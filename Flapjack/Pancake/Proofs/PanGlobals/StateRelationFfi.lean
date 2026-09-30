import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

namespace Flapjack.PanGlobalsStateRelationFfi

open Flapjack

/-- Canonical state roundtrips, re-exported for this relation theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip, re-exported for this relation theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Original HOL1564 implication: replacing both FFI states preserves the
    same relation flag, with no additional premise on the new FFI state. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_change_ffi"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem stateRelChangeFfiHOL {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ) (flag : Bool)
    (ffi : HolFfiState σ) :
    panGlobalsStateRelHOLExact flag context source target →
      panGlobalsStateRelHOLExact flag context {source with ffi := ffi} {target with ffi := ffi} := by
  intro hrel
  rcases hrel with ⟨ht, hl, hb, hbe, he, hc, hs, hts, hg, hgw, hm, hsh, hmem, _, hcode, hd⟩
  exact ⟨ht, hl, hb, hbe, he, hc, hs, hts, hg, hgw, hm, hsh, hmem, rfl, hcode, hd⟩

end Flapjack.PanGlobalsStateRelationFfi
