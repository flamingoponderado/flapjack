import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

namespace Flapjack.PanGlobalsFreshLocalMemory

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

/-- Genuine `Store` induction case of HOL1045 `evaluate_fresh_local`.
No success, address-validity, bounds or target-evaluation premise is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_Store {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (destination source : ExpHOL width)
    (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.store destination source) ∧
      evaluateHOLFiniteState state (.store destination source) = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
        (.store destination source) = (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hf : name ∉ varExpHOL destination ∧ name ∉ varExpHOL source := by
    simpa only [freeVarIdsHOL, List.mem_append, not_or] using h.1
  have hd := evalFreshUpdate state name value destination hf.1
  have hs := evalFreshUpdate state name value source hf.2
  have hev := h.2
  rw [evaluateHOLFiniteState_store] at hev
  refine ⟨post.locals.updateEq (name, value), ?_, fun _ => rfl⟩
  rw [evaluateHOLFiniteState_store, hd, hs]
  dsimp only at *
  repeat' split at hev
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  all_goals simp_all

/-- Genuine `Store32` induction case of HOL1045 `evaluate_fresh_local`.
No success, address-validity, bounds or target-evaluation premise is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_Store32 {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (destination source : ExpHOL width)
    (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.store32 destination source) ∧
      evaluateHOLFiniteState state (.store32 destination source) = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
        (.store32 destination source) = (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hf : name ∉ varExpHOL destination ∧ name ∉ varExpHOL source := by
    simpa only [freeVarIdsHOL, List.mem_append, not_or] using h.1
  have hd := evalFreshUpdate state name value destination hf.1
  have hs := evalFreshUpdate state name value source hf.2
  have hev := h.2
  rw [evaluateHOLFiniteState_store32] at hev
  refine ⟨post.locals.updateEq (name, value), ?_, fun _ => rfl⟩
  rw [evaluateHOLFiniteState_store32, hd, hs]
  dsimp only at *
  repeat' split at hev
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  all_goals simp_all

/-- Genuine `StoreByte` induction case of HOL1045 `evaluate_fresh_local`.
No success, address-validity, bounds or target-evaluation premise is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_StoreByte {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (destination source : ExpHOL width)
    (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.storeByte destination source) ∧
      evaluateHOLFiniteState state (.storeByte destination source) = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
        (.storeByte destination source) = (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hf : name ∉ varExpHOL destination ∧ name ∉ varExpHOL source := by
    simpa only [freeVarIdsHOL, List.mem_append, not_or] using h.1
  have hd := evalFreshUpdate state name value destination hf.1
  have hs := evalFreshUpdate state name value source hf.2
  have hev := h.2
  rw [evaluateHOLFiniteState_storeByte] at hev
  refine ⟨post.locals.updateEq (name, value), ?_, fun _ => rfl⟩
  rw [evaluateHOLFiniteState_storeByte, hd, hs]
  dsimp only at *
  repeat' split at hev
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  all_goals simp_all

end Flapjack.PanGlobalsFreshLocalMemory
