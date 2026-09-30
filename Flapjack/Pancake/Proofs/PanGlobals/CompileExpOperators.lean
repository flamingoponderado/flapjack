import Flapjack.Pancake.Proofs.PanGlobals.CompileExpRStruct

namespace Flapjack.PanGlobalsCompileExpOperators
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

/-- Original Op case with only pointwise recursive expression IHs. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectOpHOL {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width)
    (operator : BinOp) (expressions : List (ExpHOL width)) (value : ValueHOL width) :
    letI : DecidablePred source.memaddrs := fun a => Classical.propDecidable (source.memaddrs a)
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    (∀ e ∈ expressions, ∀ result,
      panGlobalsStateRelHOLExact true context source target ∧
        source.evalHOLFinite e = some result →
      target.evalHOLFinite (compileExpExactHOL context e) = some result) →
    panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite (.op operator expressions) = some value →
    target.evalHOLFinite (compileExpExactHOL context (.op operator expressions)) = some value := by
  classical
  intro ih ⟨hrel, heval⟩
  cases hs : evalListHOLExact source.toExact expressions with
  | none => simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, hs] at heval
  | some vs =>
    have ht := PanGlobalsCompileExpRStruct.evalCompiledList source.toExact target.toExact context expressions
      (fun e he v hv => ih e he v ⟨hrel, hv⟩) vs hs
    simpa [compileExpExactHOL, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, ht, hs]
      using heval

/-- Original Panop case with only pointwise recursive expression IHs. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectPanopHOL {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width)
    (operator : PanOp) (expressions : List (ExpHOL width)) (value : ValueHOL width) :
    letI : DecidablePred source.memaddrs := fun a => Classical.propDecidable (source.memaddrs a)
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    (∀ e ∈ expressions, ∀ result,
      panGlobalsStateRelHOLExact true context source target ∧
        source.evalHOLFinite e = some result →
      target.evalHOLFinite (compileExpExactHOL context e) = some result) →
    panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite (.panop operator expressions) = some value →
    target.evalHOLFinite (compileExpExactHOL context (.panop operator expressions)) = some value := by
  classical
  intro ih ⟨hrel, heval⟩
  cases hs : evalListHOLExact source.toExact expressions with
  | none => simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, hs] at heval
  | some vs =>
    have ht := PanGlobalsCompileExpRStruct.evalCompiledList source.toExact target.toExact context expressions
      (fun e he v hv => ih e he v ⟨hrel, hv⟩) vs hs
    simpa [compileExpExactHOL, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, ht, hs]
      using heval

end Flapjack.PanGlobalsCompileExpOperators
