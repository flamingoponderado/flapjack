import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

namespace Flapjack.PanGlobalsStateRelationClock

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

/-- HOL891-896: decreasing both clocks preserves the original relation at
    the same flag, without any clock positivity or extra state premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_dec_clock"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem stateRelDecClockHOL {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ) (flag : Bool) :
    panGlobalsStateRelHOLExact flag context source target →
      panGlobalsStateRelHOLExact flag context
        source.decClockHOLFinite target.decClockHOLFinite := by
  intro hrel
  have hc := hrel.2.2.2.2.2.1
  exact ⟨hrel.1, hrel.2.1, hrel.2.2.1, hrel.2.2.2.1, hrel.2.2.2.2.1,
    congrArg (fun clock : Nat => clock - 1) hc, hrel.2.2.2.2.2.2⟩

end Flapjack.PanGlobalsStateRelationClock
