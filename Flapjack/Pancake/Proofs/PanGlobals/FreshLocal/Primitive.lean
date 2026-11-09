module

public import Flapjack.Pancake.Proofs.PanGlobals
public import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
public import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Support

@[expose] public section

namespace Flapjack.PanGlobalsFreshLocalPrimitive

open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.PanGlobalsFreshLocalSupport

/-- Canonical finite state roundtrip; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Genuine Primitive case; no extra premises. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_Primitive {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (target : MlS) (operator : PrimOp)
    (source : List (ExpHOL width)) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.primitive target operator source) ∧
      evaluateHOLFiniteState state (.primitive target operator source) = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
        (.primitive target operator source) = (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hf : name ≠ target ∧ name ∉ (source.map varExpHOL).flatten := by
    simpa only [freeVarIdsHOL, List.mem_cons, not_or] using h.1
  have he := evalFreshUpdateList state name value source hf.2
  have hv : ∀ assigned : ValueHOL width,
      isValidValueHOLFinite {state with locals := state.locals.updateEq (name, value)}
          .local target assigned = isValidValueHOLFinite state .local target assigned := by
    intro assigned
    simp only [isValidValueHOLFinite, lookupKvarHOLFinite,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, if_neg (Ne.symm hf.1)]
  have hu : ∀ assigned : ValueHOL width,
      setVarHOLFinite target assigned
          {state with locals := state.locals.updateEq (name, value)} =
        {setVarHOLFinite target assigned state with
          locals := (setVarHOLFinite target assigned state).locals.updateEq (name, value)} := by
    intro assigned
    have hm : (state.locals.updateEq (name, value)).update (target, assigned) =
        (state.locals.update (target, assigned)).updateEq (name, value) := by
      apply HolFiniteMapExact.ext
      funext key
      by_cases hk : key = name
      · subst key
        simp [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq,
          FUPDATE_HOL, FUPDATE, beq_iff_eq, Ne.symm hf.1]
      · simp [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq,
          FUPDATE_HOL, FUPDATE, beq_iff_eq, hk]
    simpa only [setVarHOLFinite] using
      congrArg (fun locals => {state with locals := locals}) hm
  have hev := h.2
  rw [evaluateHOLFiniteState_primitive] at hev
  refine ⟨post.locals.updateEq (name, value), ?_, fun _ => rfl⟩
  rw [evaluateHOLFiniteState_primitive, he]
  simp only [hv]
  repeat' split at hev
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  all_goals simp_all

end Flapjack.PanGlobalsFreshLocalPrimitive
