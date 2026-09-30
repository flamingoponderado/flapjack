import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

namespace Flapjack.PanGlobalsFreshLocalShMemLoad

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

/-- Flapjack-specific keyed shared-memory write commutes with a fresh local
binding at the internally derived distinct local names. No separate HOL
declaration; it only packages `set_kvar` and the `ffi` update. -/
private theorem setKvarFfiHOLFinite_freshUpdate {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (kind : VarKind) (target : MlS)
    (written : ValueHOL width) (newFfi : HolFfiState σ) (name : MlS) (value : ValueHOL width)
    (hname : kind = .local → name ≠ target) :
    setKvarFfiHOLFinite kind target written
        {state with locals := state.locals.updateEq (name, value)} newFfi =
      {setKvarFfiHOLFinite kind target written state newFfi with
        locals :=
          (setKvarFfiHOLFinite kind target written state newFfi).locals.updateEq (name, value)} := by
  cases kind with
  | «local» =>
    have hne : name ≠ target := hname rfl
    have hm : (state.locals.updateEq (name, value)).update (target, written) =
        (state.locals.update (target, written)).updateEq (name, value) := by
      apply HolFiniteMapExact.ext
      funext key
      by_cases hk : key = name
      · subst key
        simp [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq,
          FUPDATE_HOL, FUPDATE, beq_iff_eq, Ne.symm hne]
      · simp [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq,
          FUPDATE_HOL, FUPDATE, beq_iff_eq, hk]
    cases state
    simp only [setKvarFfiHOLFinite, setKvarHOLFinite, setVarHOLFinite,
      PanSemStateFiniteExact.mk.injEq]
    repeat' constructor
    all_goals try rfl
    exact hm
  | «global» =>
    cases state
    simp [setKvarFfiHOLFinite, setKvarHOLFinite, setGlobalHOLFinite]

/-- Flapjack-specific transport of the shared-memory load under a fresh local
binding. The `nb`/address-domain/FFI branches are identical because they read
only fields the locals update leaves unchanged; on a successful return the
keyed write commutes with the fresh binding at the internally derived distinct
local names, while a final FFI event clears locals in both states. -/
private theorem shMemLoadHOLFiniteExact_freshUpdate {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.shMemaddrs]
    (kind : VarKind) (target : MlS)
    (addr : RiscV.Word width) (nb : Nat) (name : MlS) (value : ValueHOL width)
    (hname : kind = .local → name ≠ target) :
    let loaded := shMemLoadHOLFiniteExact state kind target addr nb
    let updated := shMemLoadHOLFiniteExact
      {state with locals := state.locals.updateEq (name, value)} kind target addr nb
    (loaded.1 = some .error ∧
      updated = (some .error,
        {loaded.2 with locals := loaded.2.locals.updateEq (name, value)})) ∨
    (loaded.1 = none ∧
      updated = (none,
        {loaded.2 with locals := loaded.2.locals.updateEq (name, value)})) ∨
    (∃ event, loaded.1 = some (.finalFfi event) ∧ updated = (some (.finalFfi event), loaded.2)) := by
  classical
  by_cases hnb : nb = 0
  · simp only [shMemLoadHOLFiniteExact, if_pos hnb]
    by_cases haddr : state.shMemaddrs addr
    · simp only [if_pos haddr]
      cases hffi : callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL addr false) with
      | final event =>
          right; right
          exact ⟨event, by simp, by simp [emptyLocalsHOLFinite]⟩
      | ret newFfi newBytes =>
          right; left
          refine ⟨by simp, ?_⟩
          simpa using setKvarFfiHOLFinite_freshUpdate state kind target
              (.val (.word (panWordOfBytesHOL false 0 newBytes))) newFfi name value hname
    · simp only [if_neg haddr]
      left
      exact ⟨by simp, by simp⟩
  · simp only [shMemLoadHOLFiniteExact, if_neg hnb]
    by_cases haddr : state.shMemaddrs (panByteAlignHOL addr)
    · simp only [if_pos haddr]
      cases hffi : callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL addr false) with
      | final event =>
          right; right
          exact ⟨event, by simp, by simp [emptyLocalsHOLFinite]⟩
      | ret newFfi newBytes =>
          right; left
          refine ⟨by simp, ?_⟩
          simpa using setKvarFfiHOLFinite_freshUpdate state kind target
              (.val (.word (panWordOfBytesHOL false 0 newBytes))) newFfi name value hname
    · simp only [if_neg haddr]
      left
      exact ⟨by simp, by simp⟩

/-- Genuine `ShMemLoad` induction case of HOL1045 `evaluate_fresh_local`.
The address expression, the `lookup_kvar` gate and the shared-memory/FFI
primitive all run unchanged because the fresh local is absent; the original
existential post-`locals` and conditional `good_res`/non-`Error` update are
retained. A final FFI event clears locals and is not `good_res`, so its
post-state is unchanged. No success, address-validity or target-evaluation
premise is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_ShMemLoad {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (operator : OpSize) (kind : VarKind)
    (target : MlS) (address : ExpHOL width)
    (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.shMemLoad operator kind target address) ∧
      evaluateHOLFiniteState state (.shMemLoad operator kind target address) = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
        (.shMemLoad operator kind target address) = (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hf : name ∉ varExpHOL address := by
    cases kind <;> simp_all [freeVarIdsHOL]
  have hname : kind = .local → name ≠ target := by
    intro hk
    subst hk
    have hconj : name ≠ target ∧ name ∉ varExpHOL address := by
      simpa only [freeVarIdsHOL, ↓reduceIte, List.mem_cons, not_or] using h.1
    exact hconj.1
  have he := evalFreshUpdate state name value address hf
  have he' : @evalHOLExact width σ _
      ({state with locals := state.locals.updateEq (name, value)} :
        PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable
        (({state with locals := state.locals.updateEq (name, value)} :
          PanSemStateFiniteExact width σ).memaddrs address)) address =
    @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) address := by
    simpa using he
  have hlook : lookupKvarHOLFinite kind target
        {state with locals := state.locals.updateEq (name, value)} =
      lookupKvarHOLFinite kind target state := by
    cases kind with
    | «local» =>
      simp only [lookupKvarHOLFinite, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
      rw [if_neg (Ne.symm (hname rfl))]
    | «global» => rfl
  have hev := h.2
  rw [evaluateHOLFiniteState_shMemLoad_source] at hev
  rw [evaluateHOLFiniteState_shMemLoad_source]
  simp only [evalHOLFinite] at hev ⊢
  rw [he']
  rw [hlook]
  cases hA : @evalHOLExact width σ _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) address with
  | none =>
      simp only [hA] at hev ⊢
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
  | some v =>
      cases v with
      | rStruct fields =>
          simp only [hA] at hev ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
          exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
      | nStruct structName fields =>
          simp only [hA] at hev ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
          exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
      | val payload =>
          cases payload with
          | word addr =>
              cases hL : lookupKvarHOLFinite kind target state with
              | none =>
                  simp only [hA, hL] at hev ⊢
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                  exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
              | some lv =>
                  cases lv with
                  | val lpayload =>
                      cases lpayload with
                      | word loadedWord =>
                          cases hl : shMemLoadHOLFiniteExact state kind target addr
                              (nbOpHOL operator) with
                          | mk lres lpost =>
                              simp only [hA, hL, hl] at hev
                              have hrel := shMemLoadHOLFiniteExact_freshUpdate state kind target
                                addr (nbOpHOL operator) name value hname
                              rw [hl] at hrel
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                              rcases hrel with ⟨he1, hupd⟩ | ⟨hn1, hupd⟩ | ⟨ev, he1, hupd⟩
                              · dsimp only [Prod.fst, Prod.snd] at he1 hupd
                                refine ⟨lpost.locals.updateEq (name, value), ?_, fun _ => rfl⟩
                                simp [hupd, he1]
                              · dsimp only [Prod.fst, Prod.snd] at hn1 hupd
                                refine ⟨lpost.locals.updateEq (name, value), ?_, fun _ => rfl⟩
                                simp [hupd, hn1]
                              · dsimp only [Prod.fst, Prod.snd] at he1 hupd
                                refine ⟨lpost.locals, ?_, ?_⟩
                                · simp [hupd, he1]
                                · intro hgood
                                  exact absurd hgood.1 (by simp [goodResHOL, he1])
                  | rStruct fs =>
                      simp only [hA, hL] at hev ⊢
                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                      exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
                  | nStruct n fs =>
                      simp only [hA, hL] at hev ⊢
                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                      exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩

end Flapjack.PanGlobalsFreshLocalShMemLoad
