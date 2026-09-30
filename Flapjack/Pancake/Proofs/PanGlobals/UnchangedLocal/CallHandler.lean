import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsUnchangedLocalCallHandler
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip re-export, with no standalone HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Genuine Call-with-handler evaluate_unchanged_local induction case.
Keeps the original unused value binder and literal guarded handler IH.
The callee replaces locals; handler entry restores caller locals before binding
the exception. No unconditional IH or extra successful-run premise is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_CallHandler {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (target : Option (VarKind × MlS))
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
      ∀ (r : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
        name ∉ freeVarIdsHOL handlerProgram ∧
        evaluateHOLFiniteState (setVarHOLFinite handlerVar exn {st with locals := state.locals})
          handlerProgram = (r, post) ∧ goodResHOL r = true ∧ r ≠ some .error →
        post.locals.lookup name =
          (setVarHOLFinite handlerVar exn {st with locals := state.locals}).locals.lookup name)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.call (some (target, some (handlerId, handlerVar, handlerProgram))) function arguments) ∧
      evaluateHOLFiniteState state (.call (some (target, some (handlerId, handlerVar, handlerProgram))) function arguments) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨hfresh, heval, hgood, herror⟩ := h
  have hn : ∀ destination, target = some (.local, destination) → name ≠ destination := by
    intro destination ht he
    subst target
    subst name
    simp [freeVarIdsHOL] at hfresh
  have hhandler : name ≠ handlerVar ∧ name ∉ freeVarIdsHOL handlerProgram := by
    cases target with
    | none =>
      simp only [freeVarIdsHOL, List.mem_append, List.mem_cons, not_or] at hfresh
      exact ⟨hfresh.1, hfresh.2.1⟩
    | some target =>
      obtain ⟨kind, destination⟩ := target
      cases kind <;> simp_all [freeVarIdsHOL]
  rw [evaluateHOLFiniteState_call] at heval
  cases ha : @evalListHOLFinite width σ _ state
      (fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none =>
    simp only [ha] at heval
    exact False.elim (herror (Prod.mk.inj heval).1.symm)
  | some values =>
    simp only [ha] at heval
    cases hl : lookupCodeHOLFinite state.code.lookup function values with
    | none =>
      simp only [hl] at heval
      exact False.elim (herror (Prod.mk.inj heval).1.symm)
    | some entry =>
      obtain ⟨body, callee, shape⟩ := entry
      simp only [hl] at heval
      by_cases hc : state.clock = 0
      · simp only [if_pos hc] at heval
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        simp [goodResHOL] at hgood
      · simp only [if_neg hc] at heval
        have hex : ∃ r st, evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (r, st) := ⟨_, _, rfl⟩
        obtain ⟨r, st, hb⟩ := hex
        simp only [hb] at heval
        cases r with
        | none => exact False.elim (herror (Prod.mk.inj heval).1.symm)
        | some r =>
          cases r with
          | «break» => exact False.elim (herror (Prod.mk.inj heval).1.symm)
          | «continue» => exact False.elim (herror (Prod.mk.inj heval).1.symm)
          | exception eid exn =>
            by_cases hid : eid = handlerId
            · simp only [if_pos hid] at heval
              cases hes : state.eshapes.lookup eid with
              | none =>
                simp only [hes] at heval
                exact False.elim (herror (Prod.mk.inj heval).1.symm)
              | some sh =>
                simp only [hes] at heval
                by_cases hg : (shapeEqHOL (shapeOfHOLExact exn) sh &&
                  isValidValueHOLExact state.toExact .local handlerVar exn) = true
                · simp only [hg, ↓reduceIte] at heval
                  have hgparts : shapeEqHOL (shapeOfHOLExact exn) sh = true ∧
                      isValidValueHOLExact state.toExact .local handlerVar exn = true := by
                    simpa using hg
                  have hs : shapeOfHOLExact exn = sh :=
                    (shapeEqHOL_eq_true _ _).mp hgparts.1
                  have hi := handlerIH values body callee shape st eid exn sh
                    ⟨ha, hl, hc, hb, hid, hes, hs, hgparts.2⟩ result post
                    ⟨hhandler.2, heval, hgood, herror⟩
                  simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                    Ne.symm hhandler.1] using hi
                · simp only [hg] at heval
                  exact False.elim (herror (Prod.mk.inj heval).1.symm)
            · simp only [if_neg hid] at heval
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              simp [goodResHOL] at hgood
          | timeOut =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
            simp [goodResHOL] at hgood
          | finalFfi event =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
            simp [goodResHOL] at hgood
          | error => exact False.elim (herror (Prod.mk.inj heval).1.symm)
          | returned ret =>
            by_cases hs : shapeEqHOL (shapeOfHOLExact ret) shape = true
            · simp only [hs, ↓reduceIte] at heval
              cases target with
              | none =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                rfl
              | some target =>
                obtain ⟨kind, destination⟩ := target
                by_cases hv : isValidValueHOLExact state.toExact kind destination ret = true
                · simp only [hv] at heval
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                  cases kind with
                  | «local» =>
                    simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update,
                      FUPDATE, Ne.symm (hn destination rfl)]
                  | «global» => rfl
                · simp only [hv] at heval
                  exact False.elim (herror (Prod.mk.inj heval).1.symm)
            · simp only [hs] at heval
              exact False.elim (herror (Prod.mk.inj heval).1.symm)

end Flapjack.PanGlobalsUnchangedLocalCallHandler
