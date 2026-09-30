import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

namespace Flapjack.PanGlobalsCompileExpCmpShift
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

/-- Cmp case: original relation/evaluation premises and the two recursive IHs only. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectCmpHOL {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width) (operator : Cmp)
    (left right : ExpHOL width) (value : ValueHOL width) :
    letI : DecidablePred source.memaddrs := fun a => Classical.propDecidable (source.memaddrs a)
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    (∀ result, panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite left = some result →
      target.evalHOLFinite (compileExpExactHOL context left) = some result) →
    (∀ result, panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite right = some result →
      target.evalHOLFinite (compileExpExactHOL context right) = some result) →
    panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite (.cmp operator left right) = some value →
    target.evalHOLFinite (compileExpExactHOL context (.cmp operator left right)) = some value := by
  classical
  intro ihl ihr ⟨hrel, heval⟩
  cases hl : evalHOLExact source.toExact left with
  | none => simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, hl] at heval
  | some vl =>
    cases hr : evalHOLExact source.toExact right with
    | none => simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, hr] at heval
    | some vr =>
      have htl := ihl vl ⟨hrel, hl⟩
      have htr := ihr vr ⟨hrel, hr⟩
      cases vl <;> cases vr <;>
        simp_all [compileExpExactHOL, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact]

/-- Shift case: original relation/evaluation premises and the two recursive IHs only. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectShiftHOL {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width) (operator : Shift)
    (left right : ExpHOL width) (value : ValueHOL width) :
    letI : DecidablePred source.memaddrs := fun a => Classical.propDecidable (source.memaddrs a)
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    (∀ result, panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite left = some result →
      target.evalHOLFinite (compileExpExactHOL context left) = some result) →
    (∀ result, panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite right = some result →
      target.evalHOLFinite (compileExpExactHOL context right) = some result) →
    panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite (.shift operator left right) = some value →
    target.evalHOLFinite (compileExpExactHOL context (.shift operator left right)) = some value := by
  classical
  intro ihl ihr ⟨hrel, heval⟩
  cases hl : evalHOLExact source.toExact left with
  | none => simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, hl] at heval
  | some vl =>
    cases hr : evalHOLExact source.toExact right with
    | none => simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, hr] at heval
    | some vr =>
      have htl := ihl vl ⟨hrel, hl⟩
      have htr := ihr vr ⟨hrel, hr⟩
      cases vl <;> cases vr <;>
        simp_all [compileExpExactHOL, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact]

end Flapjack.PanGlobalsCompileExpCmpShift
