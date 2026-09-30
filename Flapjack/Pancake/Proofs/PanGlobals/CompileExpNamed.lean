import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

namespace Flapjack.PanGlobalsCompileExpNamed
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

/-- Named-structure case of compile_exp_correct. The original state relation
    forces an empty struct context, exactly as in the HOL proof; no extra premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectNStructHOL {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width) (name : MlS)
    (fields : List (MlS × ExpHOL width)) (value : ValueHOL width) :
    letI : DecidablePred source.memaddrs := fun a => Classical.propDecidable (source.memaddrs a)
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite (.nstruct name fields) = some value →
    target.evalHOLFinite (compileExpExactHOL context (.nstruct name fields)) = some value := by
  classical
  intro ⟨hrel, heval⟩
  have hs := (panGlobalsStateRelStructsHOLExact true context source target hrel).1
  simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact,
    hs] at heval
/-- Named-structure case of compile_exp_correct. The original state relation
    forces an empty struct context, exactly as in the HOL proof; no extra premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectNFieldHOL {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width) (name : MlS)
    (expression : ExpHOL width) (value : ValueHOL width) :
    letI : DecidablePred source.memaddrs := fun a => Classical.propDecidable (source.memaddrs a)
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite (.nfield name expression) = some value →
    target.evalHOLFinite (compileExpExactHOL context (.nfield name expression)) = some value := by
  classical
  intro ⟨hrel, heval⟩
  have hs := (panGlobalsStateRelStructsHOLExact true context source target hrel).1
  cases he : evalHOLExact source.toExact expression with
  | none => simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, he] at heval
  | some v =>
    cases v <;> simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, he,
      hs] at heval

end Flapjack.PanGlobalsCompileExpNamed
