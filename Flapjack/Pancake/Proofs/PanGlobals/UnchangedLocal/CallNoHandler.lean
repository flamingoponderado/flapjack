import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.CallNoHandler

namespace Flapjack.PanGlobalsUnchangedLocalCallNoHandler
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip; no standalone HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- The non-tail Call-without-handler subcase of HOL1111-1137. The local
destination (if any) is excluded by the freshness premise, so the caller's
lookup of the fresh name is unchanged. The original unused value binder is
retained, and no premise beyond the literal statement is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_CallNoHandler {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (target : Option (VarKind × MlS))
    (function : MlS) (arguments : List (ExpHOL width)) (state : PanSemStateFiniteExact width σ) :
    ∀ (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
      name ∉ freeVarIdsHOL (.call (some (target, none)) function arguments) ∧
      evaluateHOLFiniteState state (.call (some (target, none)) function arguments) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error →
      post.locals.lookup name = state.locals.lookup name := by
  classical
  intro result post ⟨hfresh, heval, hgood, herror⟩
  have hf : name ∉ (arguments.map varExpHOL).flatten := by
    intro hm
    apply hfresh
    cases target with
    | none => simpa [freeVarIdsHOL] using hm
    | some target =>
      obtain ⟨kind, destination⟩ := target
      cases kind <;> simp [freeVarIdsHOL, hm]
  have hn : ∀ destination, target = some (.local, destination) → name ≠ destination := by
    intro destination ht he
    subst target
    subst name
    exact hfresh (by simp [freeVarIdsHOL])
  rw [evaluateHOLFiniteState_call] at heval
  cases ha : @evalListHOLFinite width σ _ state
      (fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none =>
    simp only [ha] at heval
    exact absurd (Prod.mk.inj heval).1.symm herror
  | some values =>
    simp only [ha] at heval
    cases hl : lookupCodeHOLFinite state.code.lookup function values with
    | none =>
      simp only [hl] at heval
      exact absurd (Prod.mk.inj heval).1.symm herror
    | some entry =>
      obtain ⟨body, callee, shape⟩ := entry
      simp only [hl] at heval
      by_cases hc : state.clock = 0
      · simp only [if_pos hc] at heval
        obtain ⟨hr, _⟩ := Prod.mk.inj heval
        rw [← hr] at hgood
        simp [goodResHOL] at hgood
      · simp only [if_neg hc] at heval
        have hex : ∃ r st, evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (r, st) :=
          ⟨_, _, rfl⟩
        obtain ⟨r, st, hb⟩ := hex
        simp only [hb] at heval
        cases r with
        | none =>
          obtain ⟨hr, _⟩ := Prod.mk.inj heval
          exact absurd hr.symm herror
        | some r =>
          cases r with
          | «break» =>
            obtain ⟨hr, _⟩ := Prod.mk.inj heval
            exact absurd hr.symm herror
          | «continue» =>
            obtain ⟨hr, _⟩ := Prod.mk.inj heval
            exact absurd hr.symm herror
          | exception exceptionId value =>
            simp only at heval
            obtain ⟨hr, _⟩ := Prod.mk.inj heval
            rw [← hr] at hgood
            simp [goodResHOL] at hgood
          | timeOut =>
            obtain ⟨hr, _⟩ := Prod.mk.inj heval
            rw [← hr] at hgood
            simp [goodResHOL] at hgood
          | finalFfi event =>
            obtain ⟨hr, _⟩ := Prod.mk.inj heval
            rw [← hr] at hgood
            simp [goodResHOL] at hgood
          | error =>
            obtain ⟨hr, _⟩ := Prod.mk.inj heval
            exact absurd hr.symm herror
          | returned ret =>
            simp only at heval
            by_cases hs : shapeEqHOL (shapeOfHOLExact ret) shape = true
            · simp only [hs, ↓reduceIte] at heval
              cases target with
              | none =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                rfl
              | some target =>
                obtain ⟨kind, destination⟩ := target
                by_cases hvv : isValidValueHOLExact state.toExact kind destination ret = true
                · simp only [hvv, ↓reduceIte] at heval
                  obtain ⟨rfl, hpost⟩ := Prod.mk.inj heval
                  rw [← hpost]
                  cases kind with
                  | «local» =>
                    show ((setVarHOLFinite destination ret { st with locals := state.locals }).locals.lookup name) =
                        state.locals.lookup name
                    simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update]
                    rw [← FUPDATE_HOL_eq_FUPDATE]
                    simp only [FUPDATE_HOL, if_neg (hn destination rfl)]
                  | «global» => rfl
                · simp only [hvv] at heval
                  obtain ⟨hr, _⟩ := Prod.mk.inj heval
                  exact absurd hr.symm herror
            · simp only [hs] at heval
              obtain ⟨hr, _⟩ := Prod.mk.inj heval
              exact absurd hr.symm herror

end Flapjack.PanGlobalsUnchangedLocalCallNoHandler
