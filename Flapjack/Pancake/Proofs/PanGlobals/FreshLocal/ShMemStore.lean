module

public import Flapjack.Pancake.Proofs.PanGlobals
public import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
public import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Support

@[expose] public section

namespace Flapjack.PanGlobalsFreshLocalShMemStore
open Flapjack.PanGlobalsFreshLocalSupport

open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite state roundtrip; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

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
