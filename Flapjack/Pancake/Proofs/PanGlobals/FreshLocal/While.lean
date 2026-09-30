import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Leaves
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsFreshLocalWhile
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Flapjack-only factoring of the original evaluate_fresh_local predicate,
with the fixed name/value chosen before HOL recInduct evaluate_ind. -/
private abbrev FreshLocalGoal {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (program : ProgHOL width)
    (state : PanSemStateFiniteExact width σ) : Prop :=
  ∀ (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
    ¬ name ∈ freeVarIdsHOL program ∧ evaluateHOLFiniteState state program = (res, post) →
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)} program =
        (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value))

/-- Flapjack-only finite-state bridge of expression freshness; it adds no
hypothesis beyond the original variable-list freshness. -/
private theorem evalFresh {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (condition : ExpHOL width)
    (name : MlS) (value : ValueHOL width) (hfresh : name ∉ varExpHOL condition) :
    @evalHOLFinite width σ _ {state with locals := state.locals.updateEq (name, value)}
      (fun a => Classical.propDecidable (state.memaddrs a)) condition =
    @evalHOLFinite width σ _ state
      (fun a => Classical.propDecidable (state.memaddrs a)) condition := by
  classical
  have h := evalHOLExact_updLocals_not_mem state.toExact name value condition hfresh
  have hlookup : (state.locals.updateEq (name, value)).lookup =
      FUPDATE_HOL state.locals.lookup (name, value) := by
    funext key
    simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have hup : ({state with locals := state.locals.updateEq (name, value)} :
      PanSemStateFiniteExact width σ).toExact =
      {state.toExact with locals := FUPDATE_HOL state.toExact.locals (name, value)} := by
    simp only [PanSemStateFiniteExact.toExact, hlookup]
  simpa only [evalHOLFinite, hup] using h

/-- Canonical finite state roundtrip for the representation qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Original While evaluate_ind case. All constructor witnesses, condition,
nonzero-word/nonzero-clock guards and body evaluation equalities are retained
from pan_sem_evaluate_ind_probe.out; recursive states are the actual body
post-state, without fix_clock (removed by the proved source rewrite). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_While {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (condition : ExpHOL width)
    (body : ProgHOL width) (state : PanSemStateFiniteExact width σ)
    (ihContinue : ∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
      (r : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
      (v1 : PanSemResultExact width),
      @evalHOLFinite width σ _ state
        (fun a => Classical.propDecidable (state.memaddrs a)) condition = some v2 ∧
      v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ state.clock ≠ 0 ∧
      (r, s1) = evaluateHOLFiniteState (decClockHOLFinite state) body ∧
      r = some v1 ∧ v1 = .continue →
      FreshLocalGoal name value (.while condition body) s1)
    (ihNone : ∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
      (r : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
      @evalHOLFinite width σ _ state
        (fun a => Classical.propDecidable (state.memaddrs a)) condition = some v2 ∧
      v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ state.clock ≠ 0 ∧
      (r, s1) = evaluateHOLFiniteState (decClockHOLFinite state) body ∧ r = none →
      FreshLocalGoal name value (.while condition body) s1)
    (ihBody : ∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width),
      @evalHOLFinite width σ _ state
        (fun a => Classical.propDecidable (state.memaddrs a)) condition = some v2 ∧
      v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ state.clock ≠ 0 →
      FreshLocalGoal name value body (decClockHOLFinite state))
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.while condition body) ∧
      evaluateHOLFiniteState state (.while condition body) = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
        (.while condition body) = (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hfresh := h.1
  have hf : name ∉ varExpHOL condition ∧ name ∉ freeVarIdsHOL body := by
    simpa only [freeVarIdsHOL, List.mem_append, not_or] using hfresh
  have he := evalFresh state condition name value hf.1
  have hev := h.2
  rw [evaluateHOLFiniteState_while_fixClockRewrite] at hev
  rw [evaluateHOLFiniteState_while_fixClockRewrite, he]
  cases hc : @evalHOLFinite width σ _ state
      (fun a => Classical.propDecidable (state.memaddrs a)) condition with
  | none =>
      simp only [hc] at hev ⊢
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
  | some v2 =>
      cases v2 with
      | rStruct fields =>
          simp only [hc] at hev ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
          exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
      | nStruct tag fields =>
          simp only [hc] at hev ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
          exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩
      | val lab =>
          cases lab with
          | word w =>
              simp only [hc] at hev ⊢
              by_cases hw : w ≠ 0
              · rw [if_pos hw] at hev ⊢
                by_cases hz : state.clock = 0
                · rw [if_pos hz] at hev
                  rw [if_pos hz]
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                  exact ⟨HolFiniteMapExact.empty, rfl, by simp [goodResHOL]⟩
                · rw [if_neg hz] at hev
                  rw [if_neg hz]
                  cases hb : evaluateHOLFiniteState (decClockHOLFinite state) body with
                  | mk r s1 =>
                      rw [hb] at hev
                      obtain ⟨locals, ht, hgood⟩ := ihBody (.val (.word w)) (.word w) w
                        ⟨hc, rfl, rfl, hw, hz⟩ r s1 ⟨hf.2, hb⟩
                      have ht' : evaluateHOLFiniteState
                          (decClockHOLFinite {state with locals := state.locals.updateEq (name, value)}) body =
                          (r, {s1 with locals := locals}) := ht
                      rw [ht']
                      dsimp only at hev ⊢
                      cases r with
                      | none =>
                          have hl := hgood ⟨rfl, by simp⟩
                          rw [hl]
                          exact ihNone (.val (.word w)) (.word w) w none s1
                            ⟨hc, rfl, rfl, hw, hz, hb.symm, rfl⟩ res post ⟨hfresh, hev⟩
                      | some result =>
                          cases result with
                          | «continue» =>
                              have hl := hgood ⟨rfl, by simp⟩
                              rw [hl]
                              exact ihContinue (.val (.word w)) (.word w) w (some .continue) s1 .continue
                                ⟨hc, rfl, rfl, hw, hz, hb.symm, rfl, rfl⟩ res post ⟨hfresh, hev⟩
                          | «break» =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                              exact ⟨locals, rfl, fun _ => hgood ⟨rfl, by simp⟩⟩
                          | error =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                              exact ⟨locals, rfl, by simp⟩
                          | timeOut =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                              exact ⟨locals, rfl, by simp [goodResHOL]⟩
                          | returned v =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                              exact ⟨locals, rfl, by simp [goodResHOL]⟩
                          | exception eid v =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                              exact ⟨locals, rfl, by simp [goodResHOL]⟩
                          | finalFfi event =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                              exact ⟨locals, rfl, by simp [goodResHOL]⟩
              · rw [if_neg hw] at hev ⊢
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                exact ⟨state.locals.updateEq (name, value), rfl, fun _ => rfl⟩

end Flapjack.PanGlobalsFreshLocalWhile
