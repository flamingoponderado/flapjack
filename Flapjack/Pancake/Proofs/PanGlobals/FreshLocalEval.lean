import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

namespace Flapjack.PanGlobalsFreshLocalEval
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical state roundtrip, re-exported for this module's map qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Source1020-1030: updating a local absent from every expression's variable
list preserves the literal OPT_MMAP evaluation. Memory decisions are internal;
the update changes only locals, so both evaluators use the same memory domain. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "OPT_MMAP_eval_fresh_var"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalListFreshVar {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (expressions : List (ExpHOL width))
    (name : MlS) (value : ValueHOL width) :
    letI : DecidablePred state.memaddrs := fun a => Classical.propDecidable (state.memaddrs a)
    letI : DecidablePred (setVarHOLFinite name value state).memaddrs :=
      fun a => Classical.propDecidable ((setVarHOLFinite name value state).memaddrs a)
    name ∉ (expressions.map varExpHOL).flatten →
      evalListHOLFinite (setVarHOLFinite name value state) expressions =
        evalListHOLFinite state expressions := by
  classical
  intro hfresh
  have h := evalListHOLExact_updLocals_not_mem state.toExact name value expressions hfresh
  have hup : (setVarHOLFinite name value state).toExact =
      { state.toExact with locals := FUPDATE_HOL state.toExact.locals (name, value) } := by
    rw [toExact_setVarHOLFinite]
    rfl
  simpa only [evalListHOLFinite, hup] using h

/-- Source1032-1045: the two original independent freshness premises permit
two sequential local updates. No distinct-name premise is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "OPT_MMAP_eval_two_fresh_vars"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalListTwoFreshVars {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (expressions : List (ExpHOL width))
    (name1 : MlS) (value1 : ValueHOL width) (name2 : MlS) (value2 : ValueHOL width) :
    letI : DecidablePred state.memaddrs := fun a => Classical.propDecidable (state.memaddrs a)
    letI : DecidablePred (setVarHOLFinite name2 value2
        (setVarHOLFinite name1 value1 state)).memaddrs :=
      fun a => Classical.propDecidable ((setVarHOLFinite name2 value2
        (setVarHOLFinite name1 value1 state)).memaddrs a)
    name1 ∉ (expressions.map varExpHOL).flatten ∧
      name2 ∉ (expressions.map varExpHOL).flatten →
      evalListHOLFinite (setVarHOLFinite name2 value2
        (setVarHOLFinite name1 value1 state)) expressions =
        evalListHOLFinite state expressions := by
  classical
  intro hfresh
  exact (evalListFreshVar (setVarHOLFinite name1 value1 state) expressions
    name2 value2 hfresh.2).trans (evalListFreshVar state expressions name1 value1 hfresh.1)

end Flapjack.PanGlobalsFreshLocalEval
