module

public import Flapjack.Pancake.Proofs.PanGlobals
public import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
public import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
public import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Support

@[expose] public section

namespace Flapjack.PanGlobalsFreshLocalTailCall

open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.PanGlobalsFreshLocalSupport

/-- Canonical finite state roundtrip; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

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
  have he := evalFreshUpdateList state name value arguments hf
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
