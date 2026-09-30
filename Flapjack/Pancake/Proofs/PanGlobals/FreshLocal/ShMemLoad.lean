import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocalEval

namespace Flapjack.PanGlobalsFreshLocalShMemLoad
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip; no standalone HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical Boolean/equality update commutation; local infrastructure. -/
private theorem updateMixed {width : Nat} [NeZero width] (map : HolFiniteMapExact MlS (ValueHOL width))
    (a b : MlS) (x y : ValueHOL width) (hne : a ≠ b) :
    (map.updateEq (a, x)).update (b, y) = (map.update (b, y)).updateEq (a, x) := by
  have he := FUPDATE_comm map.lookup a x b y hne
  cases map
  simp only [HolFiniteMapExact.update, HolFiniteMapExact.updateEq, FUPDATE_HOL_eq_FUPDATE]
  congr 1

/-- Local factoring of the shared-memory transition's fresh-local relation;
no standalone HOL declaration. It retains final-event local clearing. -/
private theorem loadFresh {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (kind : VarKind) (destination : MlS)
    (address : BitVec width) (nb : Nat) (state : PanSemStateFiniteExact width σ)
    (hne : kind = .local → name ≠ destination)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : @shMemLoadHOLFiniteExact width σ _ state
      (fun a => Classical.propDecidable (state.shMemaddrs a)) kind destination address nb = (result, post)) :
    ∃ locals,
      @shMemLoadHOLFiniteExact width σ _ {state with locals := state.locals.updateEq (name, value)}
        (fun a => Classical.propDecidable (state.shMemaddrs a)) kind destination address nb =
        (result, {post with locals := locals}) ∧
      (goodResHOL result = true ∧ result ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  by_cases hn : nb = 0
  · by_cases ha : state.shMemaddrs address
    · simp only [shMemLoadHOLFiniteExact, if_pos hn, if_pos ha] at heval ⊢
      cases hh : callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL address false) <;> simp only [hh] at heval ⊢
      case final event =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        exact ⟨HolFiniteMapExact.empty, rfl, by simp [goodResHOL]⟩
      case ret newFfi newBytes =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        refine ⟨_, ?_, fun _ => rfl⟩
        cases kind <;> simp_all [setKvarFfiHOLFinite, setKvarHOLFinite,
          setVarHOLFinite, setGlobalHOLFinite, updateMixed]
    · simp only [shMemLoadHOLFiniteExact, if_pos hn, if_neg ha] at heval ⊢
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
  · by_cases ha : state.shMemaddrs (panByteAlignHOL address)
    · simp only [shMemLoadHOLFiniteExact, if_neg hn, if_pos ha] at heval ⊢
      cases hh : callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL address false) <;> simp only [hh] at heval ⊢
      case final event =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        exact ⟨HolFiniteMapExact.empty, rfl, by simp [goodResHOL]⟩
      case ret newFfi newBytes =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        refine ⟨_, ?_, fun _ => rfl⟩
        cases kind <;> simp_all [setKvarFfiHOLFinite, setKvarHOLFinite,
          setVarHOLFinite, setGlobalHOLFinite, updateMixed]
    · simp only [shMemLoadHOLFiniteExact, if_neg hn, if_neg ha] at heval ⊢
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩

/-- Genuine ShMemLoad case of evaluate_fresh_local1045-1091, with original
freshness, source evaluation, existential locals and conditional update. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_ShMemLoad {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (operator : OpSize) (kind : VarKind)
    (destination : MlS) (address : ExpHOL width) (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.shMemLoad operator kind destination address) ∧
      evaluateHOLFiniteState state (.shMemLoad operator kind destination address) = (result, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
        (.shMemLoad operator kind destination address) = (result, {post with locals := locals}) ∧
      (goodResHOL result = true ∧ result ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hf : name ∉ varExpHOL address := by
    intro hm
    apply h.1
    cases kind <;> simp [freeVarIdsHOL, hm]
  have hn : kind = .local → name ≠ destination := by
    intro hk he
    subst kind
    subst name
    simpa [freeVarIdsHOL] using h.1
  have hup : ({state with locals := state.locals.updateEq (name, value)} :
      PanSemStateFiniteExact width σ).toExact =
      {state.toExact with locals := FUPDATE_HOL state.toExact.locals (name, value)} := rfl
  have hg := evalHOLExact_updLocals_not_mem state.toExact name value address hf
  have hguard : @evalHOLFinite width σ _
      {state with locals := state.locals.updateEq (name, value)}
      (fun a => Classical.propDecidable (state.memaddrs a)) address =
      @evalHOLFinite width σ _ state
      (fun a => Classical.propDecidable (state.memaddrs a)) address := by
    simpa only [evalHOLFinite, hup] using hg
  have hlookup : lookupKvarHOLFinite kind destination
      {state with locals := state.locals.updateEq (name, value)} =
      lookupKvarHOLFinite kind destination state := by
    cases kind with
    | «local» => simp [lookupKvarHOLFinite, HolFiniteMapExact.updateEq, FUPDATE_HOL, Ne.symm (hn rfl)]
    | «global» => rfl
  have heval := h.2
  rw [evaluateHOLFiniteState_shMemLoad_source] at heval ⊢
  simp only [hguard, hlookup]
  cases he : @evalHOLFinite width σ _ state
      (fun a => Classical.propDecidable (state.memaddrs a)) address <;>
    simp only [he] at heval ⊢
  case none =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
    exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
  case some v =>
    cases v with
    | rStruct fs =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
    | nStruct n fs =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
    | val w =>
      cases w with
      | word a =>
        cases hl : lookupKvarHOLFinite kind destination state <;> simp only [hl] at heval ⊢
        case none =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
        case some v =>
          cases v with
          | rStruct fs =>
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
          | nStruct n fs =>
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
          | val w =>
              cases w with
              | word w => exact loadFresh name value kind destination a (nbOpHOL operator) state hn result post heval

end Flapjack.PanGlobalsFreshLocalShMemLoad
