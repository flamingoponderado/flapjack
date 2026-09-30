import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

namespace Flapjack.PanGlobalsFreshLocalTailCall

open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite state roundtrip; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Flapjack-specific transport of existing broad expression freshness through
the canonical state codec. The domain decision is internal, not a premise. -/
private theorem evalFreshUpdate {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (value : ValueHOL width)
    (expression : List (ExpHOL width)) (h : name ∉ (expression.map varExpHOL).flatten) :
    @evalListHOLExact width σ _
      ({state with locals := state.locals.updateEq (name, value)} :
        PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
    @evalListHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression := by
  classical
  have hlookup : (state.locals.updateEq (name, value)).lookup =
      FUPDATE_HOL state.locals.lookup (name, value) := by
    funext key
    exact HolFiniteMapExact.lookup_updateEq _ _ _
  simpa only [toExact_setLocals, hlookup] using
    (@evalListHOLExact_updLocals_not_mem width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) name value expression h)

/-- Source Call NONE tail-call branch. Caller locals are overwritten at callee
entry, so no body simulation premise is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_CallNone {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (function : MlS)
    (arguments : List (ExpHOL width)) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.call none function arguments) ∧
      evaluateHOLFiniteState state (.call none function arguments) = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
        (.call none function arguments) = (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hf : name ∉ (arguments.map varExpHOL).flatten := by
    simpa only [freeVarIdsHOL] using h.1
  have he := evalFreshUpdate state name value arguments hf
  have hc : ∀ callee : HolFiniteMapExact MlS (ValueHOL width),
      callEntryStateHOLFinite {state with locals := state.locals.updateEq (name, value)} callee =
        callEntryStateHOLFinite state callee := fun _ => rfl
  have hev := h.2
  rw [evaluateHOLFiniteState_call] at hev
  rw [evaluateHOLFiniteState_call]
  simp only [evalListHOLFinite, he, hc] at hev ⊢
  repeat' split at hev
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  all_goals refine ⟨(evaluateHOLFiniteState
    {state with locals := state.locals.updateEq (name, value)}
    (.call none function arguments)).2.locals, ?_, ?_⟩
  all_goals simp_all [evaluateHOLFiniteState_call, evalListHOLFinite, goodResHOL, emptyLocalsHOLFinite]
  all_goals cases ‹PanSemResultExact width› <;> simp_all

end Flapjack.PanGlobalsFreshLocalTailCall
