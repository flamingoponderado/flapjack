import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact
import Flapjack.Pancake.Semantics.PanSem.EvalFinite

namespace Flapjack.PanGlobalsCompileExpRField

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

/-- RField case of source `compile_exp_correct`. Only the recursive
subexpression induction hypothesis is added to the original premises. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectRFieldHOL {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width) (index : Nat)
    (expression : ExpHOL width) (value : ValueHOL width) :
    letI : DecidablePred source.memaddrs := fun a => Classical.propDecidable (source.memaddrs a)
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    (∀ result, panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite expression = some result →
      target.evalHOLFinite (compileExpExactHOL context expression) = some result) →
    panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite (.rfield index expression) = some value →
    target.evalHOLFinite (compileExpExactHOL context (.rfield index expression)) = some value := by
  classical
  intro ih ⟨hrel, heval⟩
  rw [PanSemStateFiniteExact.evalHOLFinite_rfield] at heval
  cases harg : evalHOLExact source.toExact expression with
  | none => simp [harg] at heval
  | some result =>
    have ht := ih result ⟨hrel, harg⟩
    cases result <;>
      simp_all [compileExpExactHOL, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact]

end Flapjack.PanGlobalsCompileExpRField
