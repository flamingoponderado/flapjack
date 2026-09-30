import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

namespace Flapjack.PanGlobalsCompileExpRStruct

open Flapjack
open Flapjack.Pancake.PanLang

/-- List recursion support for the RStruct induction case; not a separate
HOL declaration. It propagates successful evaluation using only pointwise IHs. -/
theorem evalCompiledList {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateExact width σ)
    [DecidablePred source.memaddrs] [DecidablePred target.memaddrs]
    (context : PanGlobalsContextExact width) (expressions : List (ExpHOL width))
    (ih : ∀ e ∈ expressions, ∀ v, evalHOLExact source e = some v →
      evalHOLExact target (compileExpExactHOL context e) = some v)
    (values : List (ValueHOL width))
    (heval : evalListHOLExact source expressions = some values) :
    evalListHOLExact target (compileExpExactHOLList context expressions) = some values := by
  induction expressions generalizing values with
  | nil => simpa [evalListHOLExact, compileExpExactHOLList] using heval
  | cons e es induction =>
    simp only [evalListHOLExact] at heval
    cases hhead : evalHOLExact source e with
    | none => simp [hhead] at heval
    | some v =>
      cases htail : evalListHOLExact source es with
      | none => simp [hhead, htail] at heval
      | some vs =>
        have hvalue : v :: vs = values := by simpa [hhead, htail] using heval
        subst values
        have hh := ih e (by simp) v hhead
        have ht := induction (fun e he => ih e (by simp [he])) vs htail
        simp [compileExpExactHOLList, evalListHOLExact, hh, ht]

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

/-- RStruct case of source compile_exp_correct; the only extra premise is
the pointwise recursive expression IH. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectRStructHOL {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width)
    (expressions : List (ExpHOL width)) (value : ValueHOL width) :
    letI : DecidablePred source.memaddrs := fun a => Classical.propDecidable (source.memaddrs a)
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    (∀ e ∈ expressions, ∀ result,
      panGlobalsStateRelHOLExact true context source target ∧
        source.evalHOLFinite e = some result →
      target.evalHOLFinite (compileExpExactHOL context e) = some result) →
    panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite (.rstruct expressions) = some value →
    target.evalHOLFinite (compileExpExactHOL context (.rstruct expressions)) = some value := by
  classical
  intro ih ⟨hrel, heval⟩
  change (evalListHOLExact source.toExact expressions).map ValueHOL.rStruct = some value at heval
  cases hs : evalListHOLExact source.toExact expressions with
  | none => simp [hs] at heval
  | some vs =>
    have ht := evalCompiledList source.toExact target.toExact context expressions
      (fun e he v hv => ih e he v ⟨hrel, hv⟩) vs hs
    simpa [compileExpExactHOL, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, ht, hs]
      using heval

end Flapjack.PanGlobalsCompileExpRStruct
