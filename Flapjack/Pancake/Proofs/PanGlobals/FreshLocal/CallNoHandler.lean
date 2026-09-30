import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.If
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsFreshLocalCallNoHandler
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip re-export, with no standalone HOL original. -/
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

/-- Genuine non-tail Call-without-handler source subcase of evaluate_fresh_local.
Callee entry replaces caller locals, so the child run is identical and needs no
additional run premise. The original existential and conditional update remain. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_CallNoHandler {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (target : Option (VarKind × MlS))
    (function : MlS) (arguments : List (ExpHOL width)) (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.call (some (target, none)) function arguments) ∧
      evaluateHOLFiniteState state (.call (some (target, none)) function arguments) = (result, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
        (.call (some (target, none)) function arguments) = (result, {post with locals := locals}) ∧
      (goodResHOL result = true ∧ result ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hf : name ∉ (arguments.map varExpHOL).flatten := by
    intro hm
    apply h.1
    cases target with
    | none => simpa [freeVarIdsHOL] using hm
    | some target =>
      obtain ⟨kind, destination⟩ := target
      cases kind <;> simp [freeVarIdsHOL, hm]
  have hn : ∀ destination, target = some (.local, destination) → name ≠ destination := by
    intro destination ht he
    subst target
    subst name
    simpa [freeVarIdsHOL] using h.1
  have hup : ({state with locals := state.locals.updateEq (name, value)} :
      PanSemStateFiniteExact width σ).toExact =
      {state.toExact with locals := FUPDATE_HOL state.toExact.locals (name, value)} := rfl
  have hargs := evalListHOLExact_updLocals_not_mem state.toExact name value arguments hf
  have hargsEq : @evalListHOLFinite width σ _
      {state with locals := state.locals.updateEq (name, value)}
      (fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      @evalListHOLFinite width σ _ state
      (fun a => Classical.propDecidable (state.memaddrs a)) arguments := by
    simpa only [evalListHOLFinite, hup] using hargs
  have heval := h.2
  rw [evaluateHOLFiniteState_call] at heval ⊢
  simp only [hargsEq]
  cases ha : @evalListHOLFinite width σ _ state
      (fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none =>
    simp only [ha] at heval ⊢
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
    exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
  | some values =>
    simp only [ha] at heval ⊢
    cases hl : lookupCodeHOLFinite state.code.lookup function values with
    | none =>
      simp only [hl] at heval ⊢
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
    | some entry =>
      obtain ⟨body, callee, shape⟩ := entry
      simp only [hl] at heval ⊢
      by_cases hc : state.clock = 0
      · simp only [if_pos hc] at heval ⊢
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        exact ⟨HolFiniteMapExact.empty, rfl, by simp [goodResHOL]⟩
      · simp only [if_neg hc] at heval ⊢
        have hentry : callEntryStateHOLFinite
            {state with locals := state.locals.updateEq (name, value)} callee =
            callEntryStateHOLFinite state callee := rfl
        rw [hentry]
        have hex : ∃ r st, evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (r, st) := ⟨_, _, rfl⟩
        obtain ⟨r, st, hb⟩ := hex
        simp only [hb] at heval ⊢
        cases r with
        | none =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          exact ⟨st.locals, rfl, by simp [goodResHOL]⟩
        | some r =>
          cases r with
          | «break» =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
            exact ⟨st.locals, rfl, by simp [goodResHOL]⟩
          | «continue» =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
            exact ⟨st.locals, rfl, by simp [goodResHOL]⟩
          | exception eid exn =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
            exact ⟨HolFiniteMapExact.empty, rfl, by simp [goodResHOL]⟩
          | timeOut =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
            exact ⟨HolFiniteMapExact.empty, rfl, by simp [goodResHOL]⟩
          | finalFfi event =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
            exact ⟨HolFiniteMapExact.empty, rfl, by simp [goodResHOL]⟩
          | error =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
            exact ⟨HolFiniteMapExact.empty, rfl, by simp [goodResHOL]⟩
          | returned ret =>
            by_cases hs : shapeEqHOL (shapeOfHOLExact ret) shape = true
            · simp only [hs, ↓reduceIte] at heval ⊢
              cases target with
              | none =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
              | some target =>
                obtain ⟨kind, destination⟩ := target
                have hk : lookupKvarHOLExact kind destination
                    ({state with locals := state.locals.updateEq (name, value)} : PanSemStateFiniteExact width σ).toExact =
                    lookupKvarHOLExact kind destination state.toExact := by
                  cases kind with
                  | «local» => simp [lookupKvarHOLExact, HolFiniteMapExact.updateEq, FUPDATE_HOL, Ne.symm (hn destination rfl)]
                  | «global» => rfl
                have hv : isValidValueHOLExact
                    ({state with locals := state.locals.updateEq (name, value)} : PanSemStateFiniteExact width σ).toExact kind destination ret =
                    isValidValueHOLExact state.toExact kind destination ret := by
                  simp only [isValidValueHOLExact, hk]
                simp only [hv]
                by_cases hvv : isValidValueHOLExact state.toExact kind destination ret = true
                · simp only [hvv] at heval ⊢
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                  refine ⟨_, ?_, fun _ => rfl⟩
                  cases kind <;> simp_all [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite, updateMixed]
                · simp only [hvv] at heval ⊢
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                  exact ⟨st.locals, rfl, by simp [goodResHOL]⟩
            · simp only [hs] at heval ⊢
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              exact ⟨st.locals, rfl, by simp [goodResHOL]⟩

end Flapjack.PanGlobalsFreshLocalCallNoHandler
