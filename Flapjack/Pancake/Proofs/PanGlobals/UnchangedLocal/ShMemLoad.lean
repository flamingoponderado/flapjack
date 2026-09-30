import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocalEval

namespace Flapjack.PanGlobalsUnchangedLocalShMemLoad
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite-state roundtrip; no standalone HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Shared-memory lookup preservation under the original good-result premise;
local factoring infrastructure with no standalone HOL original. -/
private theorem loadUnchanged {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (kind : VarKind) (destination : MlS)
    (address : BitVec width) (nb : Nat) (state : PanSemStateFiniteExact width σ)
    (hne : kind = .local → name ≠ destination)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : @shMemLoadHOLFiniteExact width σ _ state
      (fun a => Classical.propDecidable (state.shMemaddrs a)) kind destination address nb = (result, post))
    (hgood : goodResHOL result = true) (herror : result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  by_cases hn : nb = 0
  · by_cases ha : state.shMemaddrs address
    · simp only [shMemLoadHOLFiniteExact, if_pos hn, if_pos ha] at heval
      cases hh : callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL address false) <;> simp only [hh] at heval
      case final event =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        simp [goodResHOL] at hgood
      case ret newFfi newBytes =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        cases kind <;> simp_all [setKvarFfiHOLFinite, setKvarHOLFinite,
          setVarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE]
        intro he
        exact False.elim (hne he.symm)
    · simp only [shMemLoadHOLFiniteExact, if_pos hn, if_neg ha] at heval
      exact False.elim (herror (Prod.mk.inj heval).1.symm)
  · by_cases ha : state.shMemaddrs (panByteAlignHOL address)
    · simp only [shMemLoadHOLFiniteExact, if_neg hn, if_pos ha] at heval
      cases hh : callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL address false) <;> simp only [hh] at heval
      case final event =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        simp [goodResHOL] at hgood
      case ret newFfi newBytes =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        cases kind <;> simp_all [setKvarFfiHOLFinite, setKvarHOLFinite,
          setVarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE]
        intro he
        exact False.elim (hne he.symm)
    · simp only [shMemLoadHOLFiniteExact, if_neg hn, if_neg ha] at heval
      exact False.elim (herror (Prod.mk.inj heval).1.symm)

/-- Genuine ShMemLoad case of evaluate_unchanged_local1105-1136.
Retains the unused value binder and original premises. Domain failures are
Error and final FFI is not good_res; returning loads change only their target
local (distinct by freshness), or globals. No extra domain/success premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocal_ShMemLoad {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (_value : ValueHOL width) (operator : OpSize) (kind : VarKind)
    (destination : MlS) (address : ExpHOL width) (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.shMemLoad operator kind destination address) ∧
      evaluateHOLFiniteState state (.shMemLoad operator kind destination address) = (result, post) ∧
      goodResHOL result = true ∧ result ≠ some .error) :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  obtain ⟨hfresh, heval, hgood, herror⟩ := h
  have hn : kind = .local → name ≠ destination := by
    intro hk he
    subst kind
    subst name
    simp [freeVarIdsHOL] at hfresh
  rw [evaluateHOLFiniteState_shMemLoad_source] at heval
  cases he : @evalHOLFinite width σ _ state
      (fun a => Classical.propDecidable (state.memaddrs a)) address <;>
    simp only [he] at heval
  case none =>
    exact False.elim (herror (Prod.mk.inj heval).1.symm)
  case some v =>
    cases v with
    | rStruct fs =>
        exact False.elim (herror (Prod.mk.inj heval).1.symm)
    | nStruct n fs =>
        exact False.elim (herror (Prod.mk.inj heval).1.symm)
    | val w =>
      cases w with
      | word a =>
        cases hl : lookupKvarHOLFinite kind destination state <;> simp only [hl] at heval
        case none =>
          exact False.elim (herror (Prod.mk.inj heval).1.symm)
        case some v =>
          cases v with
          | rStruct fs =>
              exact False.elim (herror (Prod.mk.inj heval).1.symm)
          | nStruct n fs =>
              exact False.elim (herror (Prod.mk.inj heval).1.symm)
          | val w =>
              cases w with
              | word w => exact loadUnchanged name kind destination a (nbOpHOL operator) state hn result post heval hgood herror

end Flapjack.PanGlobalsUnchangedLocalShMemLoad
