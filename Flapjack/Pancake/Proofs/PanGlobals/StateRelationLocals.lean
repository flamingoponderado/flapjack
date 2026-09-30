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

/-- Source961-966: identical local updates preserve the relation, with any
new locals flag. Equality of the original locals is derived from state_rel T. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_set_var"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem stateRelSetVarHOL {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ) (newFlag : Bool)
    (name : Flapjack.Pancake.PanLang.MlS) (value : ValueHOL width) :
    panGlobalsStateRelHOLExact true context source target →
      panGlobalsStateRelHOLExact newFlag context
        (source.setVarHOLFinite name value) (target.setVarHOLFinite name value) := by
  intro hrel
  refine ⟨hrel.1, ?_, hrel.2.2⟩
  intro _
  have hl := hrel.2.1 rfl
  simp only [PanSemStateFiniteExact.setVarHOLFinite, hl]

/-- Exact port of HOL `res_var_FEMPTY`
(`cakeml/pancake/proofs/pan_globalsProofScript.sml:1011-1015`): the panic-reset
finite map is unchanged when writing an `none` value into `FEMPTY`. The HOL
source uses the bare `α |-> β` finite-map carrier, rendered here with
`HolFiniteMapExact`; this is exactly the singular-map-equality qualifier's
target shape, witnessed below at the lookup level. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "res_var_FEMPTY"
  (fmap_as_finite_support_equality)]
theorem resVarFEMPTYExact {α β : Type} [DecidableEq α] (n : α) :
    HolFiniteMapExact.resVarEq (HolFiniteMapExact.empty : HolFiniteMapExact α β) (n, none) =
      (HolFiniteMapExact.empty : HolFiniteMapExact α β) := by
  apply HolFiniteMapExact.ext
  funext k
  simp only [HolFiniteMapExact.lookup_resVarEq_none, HolFiniteMapExact.lookup_empty, FDOMSUB_HOL]
  by_cases hk : k = n
  · simp [hk]
  · simp [hk]

/-- Lookup-level witness for `resVarFEMPTYExact`, required by the singular
map-equality qualifier. -/
theorem holFmapAsFiniteSupportEqualityWitness_resVarFEMPTYExact {α β : Type} [DecidableEq α]
    (n : α) (k : α) :
    (HolFiniteMapExact.resVarEq (HolFiniteMapExact.empty : HolFiniteMapExact α β) (n, none)).lookup k =
      (HolFiniteMapExact.empty : HolFiniteMapExact α β).lookup k := by
  rw [resVarFEMPTYExact]

end Flapjack.PanGlobalsStateRelationLocals
