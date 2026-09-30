import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsUnchangedLocalCallNoHandler
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip re-export, with no standalone HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Genuine non-tail Call-without-handler evaluate_unchanged_local case.
The original good_res/non-Error premise admits only normal non-tail returns.
Caller locals are restored; a local target differs from the nonfree name.
Retains the unused value binder and adds no premise or callee IH. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_CallNoHandler {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (target : Option (VarKind × MlS))
    (function : MlS) (arguments : List (ExpHOL width)) (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.call (some (target, none)) function arguments) ∧
      evaluateHOLFiniteState state (.call (some (target, none)) function arguments) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨hfresh, heval, hgood, herror⟩ := h
  have hn : ∀ destination, target = some (.local, destination) → name ≠ destination := by
    intro destination ht he
    subst target
    subst name
    simp [freeVarIdsHOL] at hfresh
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

end Flapjack.PanGlobalsUnchangedLocalCallNoHandler
