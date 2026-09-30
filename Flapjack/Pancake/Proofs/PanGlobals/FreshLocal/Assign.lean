import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

namespace Flapjack.PanGlobalsFreshLocalAssign

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

/-- Genuine `Assign` induction case of HOL1045 `evaluate_fresh_local`.
The local target differs from the fresh name by the original free-variable
premise; no target disequality or successful evaluation is assumed separately. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_Assign {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (kind : VarKind) (target : MlS)
    (source : ExpHOL width) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.assign kind target source) ∧
      evaluateHOLFiniteState state (.assign kind target source) = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)}
        (.assign kind target source) = (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hf : name ∉ varExpHOL source := by
    cases kind <;> simp_all [freeVarIdsHOL]
  have hn : kind = .local → name ≠ target := by
    intro hk
    subst kind
    have hf' : name ≠ target ∧ name ∉ varExpHOL source := by
      simpa only [freeVarIdsHOL, ↓reduceIte, List.mem_cons, not_or] using h.1
    exact hf'.1
  have he := evalFreshUpdate state name value source hf
  have hv : ∀ assigned : ValueHOL width,
      isValidValueHOLFinite {state with locals := state.locals.updateEq (name, value)}
          kind target assigned = isValidValueHOLFinite state kind target assigned := by
    intro assigned
    cases kind with
    | «local» =>
      simp only [isValidValueHOLFinite, lookupKvarHOLFinite,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, if_neg (Ne.symm (hn rfl))]
    | «global» => rfl
  have hu : ∀ assigned : ValueHOL width,
      setKvarHOLFinite kind target assigned
          {state with locals := state.locals.updateEq (name, value)} =
        {setKvarHOLFinite kind target assigned state with
          locals := (setKvarHOLFinite kind target assigned state).locals.updateEq (name, value)} := by
    intro assigned
    cases kind with
    | «local» =>
      have hm : (state.locals.updateEq (name, value)).update (target, assigned) =
          (state.locals.update (target, assigned)).updateEq (name, value) := by
        apply HolFiniteMapExact.ext
        funext key
        by_cases hk : key = name
        · subst key
          simp [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq,
            FUPDATE_HOL, FUPDATE, beq_iff_eq, Ne.symm (hn rfl)]
        · simp [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq,
            FUPDATE_HOL, FUPDATE, beq_iff_eq, hk]
      simpa only [setKvarHOLFinite, setVarHOLFinite] using
        congrArg (fun locals => {state with locals := locals}) hm
    | «global» => rfl
  have hev := h.2
  rw [evaluateHOLFiniteState_assign] at hev
  refine ⟨post.locals.updateEq (name, value), ?_, fun _ => rfl⟩
  rw [evaluateHOLFiniteState_assign, he]
  simp only [hv]
  repeat' split at hev
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  all_goals simp_all

end Flapjack.PanGlobalsFreshLocalAssign
