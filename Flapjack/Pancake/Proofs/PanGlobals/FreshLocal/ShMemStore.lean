import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

namespace Flapjack.PanGlobalsFreshLocalShMemStore

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

/-- Genuine `ShMemStore` induction case of HOL1045 `evaluate_fresh_local`.
No success, address-validity, bounds or target-evaluation premise is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_ShMemStore {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (operator : OpSize) (destination source : ExpHOL width)
    (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.shMemStore operator destination source) ∧
      evaluateHOLFiniteState state (.shMemStore operator destination source) = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
        (.shMemStore operator destination source) = (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hf : name ∉ varExpHOL destination ∧ name ∉ varExpHOL source := by
    simpa only [freeVarIdsHOL, List.mem_append, not_or] using h.1
  have hd := evalFreshUpdate state name value destination hf.1
  have hs := evalFreshUpdate state name value source hf.2
  have hev := h.2
  rw [evaluateHOLFiniteState_shMemStore_total] at hev
  refine ⟨post.locals.updateEq (name, value), ?_, fun _ => rfl⟩
  rw [evaluateHOLFiniteState_shMemStore_total, hd, hs]
  dsimp only at hev ⊢
  repeat' split at hev
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  all_goals try solve | simp_all [ofExact, toExact]
  rename_i evAddr evValue addr bytes ha hb
  by_cases hn : nbOpHOL operator = 0
  · by_cases hd : state.shMemaddrs addr
    · cases hffi : callFFIHOL state.ffi (.sharedMem .mappedWrite)
        [BitVec.ofNat 8 (nbOpHOL operator)]
        (panWordToBytesHOL bytes false ++ panWordToBytesHOL addr false) <;>
        simp_all [shMemStoreHOLExact, ofExact, toExact]
    · simp_all [shMemStoreHOLExact, ofExact, toExact]
  · by_cases hd : state.shMemaddrs (panByteAlignHOL addr)
    · cases hffi : callFFIHOL state.ffi (.sharedMem .mappedWrite)
        [BitVec.ofNat 8 (nbOpHOL operator)]
        ((panWordToBytesHOL bytes false).take (nbOpHOL operator) ++ panWordToBytesHOL addr false) <;>
        simp_all [shMemStoreHOLExact, ofExact, toExact]
    · simp_all [shMemStoreHOLExact, ofExact, toExact]

end Flapjack.PanGlobalsFreshLocalShMemStore
