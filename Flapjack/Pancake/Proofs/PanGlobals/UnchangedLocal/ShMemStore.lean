import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocalEval

namespace Flapjack.PanGlobalsUnchangedLocalShMemStore
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip; no standalone HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Source store transition preserves the raw locals projection on every arm;
local factoring infrastructure, no standalone HOL declaration. -/
private theorem storeLocals {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (bytes address : BitVec width) (nb : Nat) :
    (shMemStoreHOLExact state bytes address nb).2.locals = state.locals := by
  unfold shMemStoreHOLExact
  repeat' split
  all_goals rfl

/-- Genuine ShMemStore constructor case of evaluate_unchanged_local1105-1136.
Original unused v and freshness/run/good_res/nonerror premises retained.
Both expressions use the original state; every domain/FFI arm preserves locals,
so no domain, successful-store or returning-FFI premise is required. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_ShMemStore {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (operator : OpSize)
    (address value : ExpHOL width) (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.shMemStore operator address value) ∧
      evaluateHOLFiniteState state (.shMemStore operator address value) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  have heval := h.2.1
  rw [evaluateHOLFiniteState_shMemStore_total] at heval
  cases ha : @evalHOLExact width σ _ state.toExact
      (fun key => Classical.propDecidable (state.memaddrs key)) address <;>
    simp only [ha] at heval
  case none =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
    rfl
  case some a =>
    cases a with
    | rStruct fields =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        rfl
    | nStruct count fields =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        rfl
    | val a =>
      cases a with
      | word addr =>
        cases hv : @evalHOLExact width σ _ state.toExact
            (fun key => Classical.propDecidable (state.memaddrs key)) value <;>
          simp only [hv] at heval
        case none =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
        case some v =>
          cases v with
          | rStruct fields =>
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              rfl
          | nStruct count fields =>
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              rfl
          | val v =>
              cases v with
              | word bytes =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                change (shMemStoreHOLExact state.toExact bytes addr (nbOpHOL operator)).2.locals name =
                  state.locals.lookup name
                rw [storeLocals]

end Flapjack.PanGlobalsUnchangedLocalShMemStore
