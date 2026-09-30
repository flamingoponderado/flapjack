import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

namespace Flapjack.PanGlobalsStateRelationLocals

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

/-- Source945-951: both original relation flags imply the relation after
clearing both local maps, at any new flag. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_empty_locals"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem stateRelEmptyLocalsHOL {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ) (newFlag : Bool) :
    (panGlobalsStateRelHOLExact true context source target →
      panGlobalsStateRelHOLExact newFlag context
        source.emptyLocalsHOLFinite target.emptyLocalsHOLFinite) ∧
    (panGlobalsStateRelHOLExact false context source target →
      panGlobalsStateRelHOLExact newFlag context
        source.emptyLocalsHOLFinite target.emptyLocalsHOLFinite) := by
  constructor <;> intro hrel <;>
    exact ⟨hrel.1, (fun _ => rfl), hrel.2.2⟩

/-- Source953-959: both original flags permit replacing both local maps
with the same arbitrary canonical finite map. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_change_locals"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals, locals])
  (words_as_type_indexed_bitvec)]
theorem stateRelChangeLocalsHOL {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ) (newFlag : Bool)
    (locals : HolFiniteMapExact Flapjack.Pancake.PanLang.MlS (ValueHOL width)) :
    (panGlobalsStateRelHOLExact true context source target →
      panGlobalsStateRelHOLExact newFlag context
        {source with locals := locals} {target with locals := locals}) ∧
    (panGlobalsStateRelHOLExact false context source target →
      panGlobalsStateRelHOLExact newFlag context
        {source with locals := locals} {target with locals := locals}) := by
  constructor <;> intro hrel <;>
    exact ⟨hrel.1, (fun _ => rfl), hrel.2.2⟩

end Flapjack.PanGlobalsStateRelationLocals
