import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

namespace Flapjack.PanGlobalsFreshLocalResults

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
    (expression : ExpHOL width) (h : name ∉ varExpHOL expression) :
    @evalHOLExact width σ _
      ({state with locals := state.locals.updateEq (name, value)} :
        PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
    @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression := by
  classical
  have hlookup : (state.locals.updateEq (name, value)).lookup =
      FUPDATE_HOL state.locals.lookup (name, value) := by
    funext key
    exact HolFiniteMapExact.lookup_updateEq _ _ _
  simpa only [toExact_setLocals, hlookup] using
    (@evalHOLExact_updLocals_not_mem width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) name value expression h)

/-- Genuine Return case; successful returns clear locals, while errors retain
the state. No success or shape bound is added to the source premises. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_Return {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (expression : ExpHOL width)
    (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.return expression) ∧
      evaluateHOLFiniteState state (.return expression) = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
        (.return expression) = (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hf : name ∉ varExpHOL expression := by simpa only [freeVarIdsHOL] using h.1
  have he := evalFreshUpdate state name value expression hf
  have hev := h.2
  rw [evaluateHOLFiniteState_return] at hev
  rw [evaluateHOLFiniteState_return, he]
  cases hx : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression with
  | none =>
      simp only [hx] at hev ⊢
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
  | some returned =>
      simp only [hx] at hev ⊢
      by_cases hs : sizeOfShapeWithContextHOL state.structs (shapeOfHOLExact returned) ≤ 32
      · rw [if_pos hs] at hev ⊢
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
        exact ⟨HolFiniteMapExact.empty, rfl, by simp [goodResHOL]⟩
      · rw [if_neg hs] at hev ⊢
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
        exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩

/-- Genuine Raise case; successful exceptions clear locals, while errors retain
the state. No success or shape bound is added to the source premises. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_Raise {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (exceptionId : MlS) (expression : ExpHOL width)
    (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.raise exceptionId expression) ∧
      evaluateHOLFiniteState state (.raise exceptionId expression) = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
        (.raise exceptionId expression) = (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hf : name ∉ varExpHOL expression := by simpa only [freeVarIdsHOL] using h.1
  have he := evalFreshUpdate state name value expression hf
  have hev := h.2
  rw [evaluateHOLFiniteState_raise] at hev
  rw [evaluateHOLFiniteState_raise, he]
  cases hx : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression <;>
    cases hy : state.eshapes.lookup exceptionId
  all_goals simp only [hx, hy] at hev ⊢
  all_goals try
    (obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
     exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩)
  rename_i result shape
  by_cases hs : shapeOfHOLExact result = shape ∧
      sizeOfShapeWithContextHOL state.structs (shapeOfHOLExact result) ≤ 32
  · rw [if_pos hs] at hev ⊢
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    exact ⟨HolFiniteMapExact.empty, rfl, by simp [goodResHOL]⟩
  · rw [if_neg hs] at hev ⊢
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩

end Flapjack.PanGlobalsFreshLocalResults
