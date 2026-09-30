import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

namespace Flapjack.PanGlobalsInitGlobalsShape

open Flapjack
open Flapjack.Pancake.PanLang

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

/-- HOL's initialization shape prerequisite. The classical domain decision
is internal and contributes no additional premise. Source2110-2125 retains
successful evaluation, state relation and FEVERY locals in that order. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "eval_state_rel_is_wf_shape"
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
     PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes,
     PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem evalStateRelIsWfShapeHOL {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (expression : ExpHOL width) (value : ValueHOL width)
    (localsEqual : Bool) (context : PanGlobalsContextExact width) :
    (letI : DecidablePred source.memaddrs := fun address => Classical.propDecidable (source.memaddrs address)
     source.evalHOLFinite expression = some value) ∧
      panGlobalsStateRelHOLExact localsEqual context source target ∧
      (∀ name bound, source.locals.lookup name = some bound →
        isWfShapeValueHOLExact source.structs bound = true) →
    isWfShapeNilHOL (shapeOfHOLExact value) = true := by
  classical
  rintro ⟨heval, hrel, hlocals⟩
  have hstruct := (panGlobalsStateRelStructsHOLExact
    localsEqual context source target hrel).1
  have hglobals : ∀ name bound, source.globals.lookup name = some bound →
      isWfShapeValueHOLExact source.structs bound = true := by
    intro name bound hlookup
    obtain ⟨address, _, hshape, _⟩ :=
      hrel.2.2.2.2.2.2.2.2.1 name bound hlookup
    rw [hstruct]
    rw [← isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil [] rfl bound]
    exact hshape
  have hwf := evalHOLExact_isWfShapeValueHOLExact source.toExact
    hlocals hglobals expression value heval
  have hshape := isWfShapeValueHOLExact_shapeOfHOLExact source.structs value hwf
  simpa [hstruct, isWfShapeNilHOL] using hshape

end Flapjack.PanGlobalsInitGlobalsShape
