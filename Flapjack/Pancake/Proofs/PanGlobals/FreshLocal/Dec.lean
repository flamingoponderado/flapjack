import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Leaves
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocalEval

namespace Flapjack.PanGlobalsFreshLocalDec
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite state roundtrip for the representation qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness


/-- Flapjack-only equality of the two canonical update interfaces. -/
private theorem updateEq_eq_update {width : Nat} [NeZero width]
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (entry : MlS × ValueHOL width) :
    locals.updateEq entry = locals.update entry := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.lookup_updateEq, HolFiniteMapExact.lookup_update,
    FUPDATE_HOL_eq_FUPDATE]

/-- Flapjack-only transport of the reviewed local update to literal HOL equality. -/
private theorem setVarEq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (value : ValueHOL width) :
    setVarHOLFinite name value state = {state with locals := state.locals.updateEq (name,value)} := by
  simp only [setVarHOLFinite, updateEq_eq_update]

/-- Flapjack-only transport of reviewed expression freshness to this state. -/
private theorem evalFreshUpdate {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (expression : ExpHOL width)
    (name : MlS) (value : ValueHOL width) (fresh : name ∉ varExpHOL expression) :
    @evalHOLExact width σ _
      ({state with locals := state.locals.updateEq (name,value)} : PanSemStateFiniteExact width σ).toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) expression =
      @evalHOLExact width σ _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a)) expression := by
  classical
  exact evalHOLExact_updLocals_not_mem state.toExact name value expression fresh

/-- Flapjack-only pointwise map algebra: independent updates commute. -/
private theorem updateCommute {width : Nat} [NeZero width]
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (a b : MlS)
    (x y : ValueHOL width) (hne : a ≠ b) :
    (locals.updateEq (a,x)).updateEq (b,y) =
      (locals.updateEq (b,y)).updateEq (a,x) := by
  apply HolFiniteMapExact.ext
  funext key
  by_cases ha : key = a <;> by_cases hb : key = b <;>
    simp_all [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- Flapjack-only pointwise map algebra: a later update shadows the same key. -/
private theorem updateSame {width : Nat} [NeZero width]
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (name : MlS)
    (first second : ValueHOL width) :
    (locals.updateEq (name,first)).updateEq (name,second) = locals.updateEq (name,second) := by
  apply HolFiniteMapExact.ext
  funext key
  by_cases h : key = name <;> simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h]

/-- Flapjack-only pointwise map algebra for restoring a distinct binding. -/
private theorem restoreCommute {width : Nat} [NeZero width]
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (a b : MlS)
    (x : ValueHOL width) (old : Option (ValueHOL width)) (hne : a ≠ b) :
    HolFiniteMapExact.resVarEq (locals.updateEq (a,x)) (b,old) =
      (HolFiniteMapExact.resVarEq locals (b,old)).updateEq (a,x) := by
  apply HolFiniteMapExact.ext
  funext key
  cases old <;> by_cases ha : key = a <;> by_cases hb : key = b <;>
    simp_all [HolFiniteMapExact.lookup_resVarEq_none, HolFiniteMapExact.lookup_resVarEq_some,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, FDOMSUB_HOL]

/-- Flapjack-only pointwise map algebra when the fresh name is the bound name. -/
private theorem restoreSame {width : Nat} [NeZero width]
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (name : MlS)
    (value : ValueHOL width) (old : Option (ValueHOL width)) :
    HolFiniteMapExact.resVarEq locals (name,some value) =
      (HolFiniteMapExact.resVarEq locals (name,old)).updateEq (name,value) := by
  apply HolFiniteMapExact.ext
  funext key
  cases old <;> by_cases h : key = name <;>
    simp [HolFiniteMapExact.lookup_resVarEq_none, HolFiniteMapExact.lookup_resVarEq_some,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, FDOMSUB_HOL, h]

/-- Genuine Dec case of HOL1045-1091. The sole recursive IH is the literal
initializer-success and shape-equality-gated body premise of evaluate_ind.
The original existential locals and conditional post-update are unchanged. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_Dec {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (bound : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL width) (body : ProgHOL width)
    (state : PanSemStateFiniteExact width σ)
    (bodyIH : ∀ initValue : ValueHOL width,
      @evalHOLExact width σ _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a)) initializer = some initValue ∧
      shape = shapeOfHOLExact initValue →
      ∀ result (post : PanSemStateFiniteExact width σ),
        name ∉ freeVarIdsHOL body ∧
          evaluateHOLFiniteState {state with locals := state.locals.updateEq (bound,initValue)} body = (result,post) →
        ∃ locals,
          evaluateHOLFiniteState
            {state with locals := (state.locals.updateEq (bound,initValue)).updateEq (name,value)} body =
            (result,{post with locals := locals}) ∧
          (goodResHOL result = true ∧ result ≠ some .error →
            locals = post.locals.updateEq (name,value)))
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.dec bound shape initializer body) ∧
      evaluateHOLFiniteState state (.dec bound shape initializer body) = (res,post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name,value)}
        (.dec bound shape initializer body) = (res,{post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error → locals = post.locals.updateEq (name,value)) := by
  classical
  obtain ⟨hfresh, hev⟩ := h
  have hinitFresh : name ∉ varExpHOL initializer := by
    intro hm
    apply hfresh
    simp [freeVarIdsHOL, hm]
  have hinitEq := evalFreshUpdate state initializer name value hinitFresh
  rw [evaluateHOLFiniteState_dec_total] at hev ⊢
  dsimp only at hev ⊢
  simp only [setVarEq] at hev ⊢
  rw [hinitEq]
  cases hi : @evalHOLExact width σ _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) initializer with
  | none =>
    simp only [hi] at hev ⊢
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
    exact ⟨state.locals.updateEq (name,value), rfl, fun _ => rfl⟩
  | some initValue =>
    simp only [hi] at hev ⊢
    by_cases hs : shapeEqHOL shape (shapeOfHOLExact initValue) = true
    · simp only [hs, ite_true] at hev ⊢
      by_cases hn : name = bound
      · subst bound
        simp only [updateSame] at ⊢
        cases hb : evaluateHOLFiniteState
            {state with locals := state.locals.updateEq (name,initValue)} body with
        | mk result output =>
          simp only [hb] at hev ⊢
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
          refine ⟨HolFiniteMapExact.resVarEq output.locals (name,some value), ?_, ?_⟩
          · simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ite_true]
          · intro _
            exact restoreSame output.locals name value (state.locals.lookup name)
      · have hbodyFresh : name ∉ freeVarIdsHOL body := by
          intro hm
          apply hfresh
          simp [freeVarIdsHOL, List.mem_filter, hm, hn]
        have hshape : shape = shapeOfHOLExact initValue := by
          simpa only [shapeEqHOL_eq_true] using hs
        have hcomm := updateCommute state.locals name bound value initValue hn
        simp only [hcomm] at ⊢
        cases hb : evaluateHOLFiniteState
            {state with locals := state.locals.updateEq (bound,initValue)} body with
        | mk result output =>
          obtain ⟨locals, hrun, hpost⟩ := bodyIH initValue ⟨hi,hshape⟩ result output ⟨hbodyFresh,hb⟩
          simp only [hb] at hev
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
          rw [hrun]
          have hold : (state.locals.updateEq (name,value)).lookup bound = state.locals.lookup bound := by
            simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, Ne.symm hn]
          rw [hold]
          refine ⟨HolFiniteMapExact.resVarEq locals (bound,state.locals.lookup bound), rfl, ?_⟩
          intro hgood
          rw [hpost hgood]
          exact restoreCommute output.locals name bound value (state.locals.lookup bound) hn
    · simp only [hs, Bool.false_eq_true, if_false] at hev ⊢
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
      exact ⟨state.locals.updateEq (name,value), rfl, fun _ => rfl⟩

end Flapjack.PanGlobalsFreshLocalDec
