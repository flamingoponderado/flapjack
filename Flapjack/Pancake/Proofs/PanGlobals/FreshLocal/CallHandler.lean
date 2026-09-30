import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.If
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsFreshLocalCallHandler
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

/-- Genuine handler-present Call source subcase of evaluate_fresh_local.
Callee entry replaces caller locals, so the child run is identical and needs no
additional callee run premise. The handler IH retains the source guard;
only redundant tuple decomposition binders are eliminated. The original existential and conditional update remain. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_CallHandler {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (target : Option (VarKind × MlS))
    (handlerId handlerVar : MlS) (handlerProgram : ProgHOL width)
    (function : MlS) (arguments : List (ExpHOL width)) (state : PanSemStateFiniteExact width σ)
    (handlerIH : ∀ (args : List (ValueHOL width)) (body : ProgHOL width)
        (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
        (st : PanSemStateFiniteExact width σ) (eid : MlS) (exn : ValueHOL width) (sh : ShapeHOL),
      state.evalListHOLFinite (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some args ∧
      lookupCodeHOLFinite state.code.lookup function args = some (body, callee, returnShape) ∧
      state.clock ≠ 0 ∧
      evaluateHOLFiniteState {state.decClockHOLFinite with locals := callee} body = (some (.exception eid exn), st) ∧
      eid = handlerId ∧ state.eshapes.lookup eid = some sh ∧ shapeOfHOLExact exn = sh ∧
      isValidValueHOLExact state.toExact .local handlerVar exn = true →
      PanGlobalsFreshLocalIf.freshLocalGoal name value
        handlerProgram (setVarHOLFinite handlerVar exn {st with locals := state.locals}))
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.call (some (target, some (handlerId, handlerVar, handlerProgram))) function arguments) ∧
      evaluateHOLFiniteState state (.call (some (target, some (handlerId, handlerVar, handlerProgram))) function arguments) = (result, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
        (.call (some (target, some (handlerId, handlerVar, handlerProgram))) function arguments) = (result, {post with locals := locals}) ∧
      (goodResHOL result = true ∧ result ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hf : name ∉ (arguments.map varExpHOL).flatten := by
    intro hm
    apply h.1
    cases target with
    | none => simp [freeVarIdsHOL, hm]
    | some target =>
      obtain ⟨kind, destination⟩ := target
      cases kind <;> simp [freeVarIdsHOL, hm]
  have hn : ∀ destination, target = some (.local, destination) → name ≠ destination := by
    intro destination ht he
    subst target
    subst name
    simpa [freeVarIdsHOL] using h.1
  have hhandler : name ≠ handlerVar ∧ name ∉ freeVarIdsHOL handlerProgram := by
    cases target with
    | none =>
      have hh := h.1
      simp only [freeVarIdsHOL, List.mem_append, List.mem_cons, not_or] at hh
      exact ⟨hh.1, hh.2.1⟩
    | some target =>
      obtain ⟨kind, destination⟩ := target
      cases kind <;> simp_all [freeVarIdsHOL]
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
            have hv : isValidValueHOLExact
                ({state with locals := state.locals.updateEq (name, value)} : PanSemStateFiniteExact width σ).toExact .local handlerVar exn =
                isValidValueHOLExact state.toExact .local handlerVar exn := by
              simp [isValidValueHOLExact, lookupKvarHOLExact, HolFiniteMapExact.updateEq,
                FUPDATE_HOL, Ne.symm hhandler.1]
            simp only [hv]
            by_cases hid : eid = handlerId
            · simp only [if_pos hid] at heval ⊢
              cases hes : state.eshapes.lookup eid with
              | none =>
                simp only [hes] at heval ⊢
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                exact ⟨st.locals, rfl, by simp [goodResHOL]⟩
              | some sh =>
                simp only [hes] at heval ⊢
                by_cases hg : (shapeEqHOL (shapeOfHOLExact exn) sh &&
                  isValidValueHOLExact state.toExact .local handlerVar exn) = true
                · simp only [hg, ↓reduceIte] at heval ⊢
                  have hgparts : shapeEqHOL (shapeOfHOLExact exn) sh = true ∧
                      isValidValueHOLExact state.toExact .local handlerVar exn = true := by
                    simpa using hg
                  have hs : shapeOfHOLExact exn = sh := by
                    have := hgparts.1
                    exact (shapeEqHOL_eq_true _ _).mp this
                  have hi := handlerIH values body callee shape st eid exn sh
                    ⟨ha, hl, hc, hb, hid, hes, hs, hgparts.2⟩
                  obtain ⟨locals, he, hgood⟩ := hi result post ⟨hhandler.2, heval⟩
                  refine ⟨locals, ?_, hgood⟩
                  simpa only [setVarHOLFinite, updateMixed _ _ _ _ _ hhandler.1] using he
                · simp only [hg] at heval ⊢
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                  exact ⟨st.locals, rfl, by simp [goodResHOL]⟩
            · simp only [if_neg hid] at heval ⊢
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

end Flapjack.PanGlobalsFreshLocalCallHandler
