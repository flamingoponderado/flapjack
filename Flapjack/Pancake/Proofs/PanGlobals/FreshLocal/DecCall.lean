import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Leaves
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocalEval

namespace Flapjack.PanGlobalsFreshLocalDecCall
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

/-- Genuine DecCall induction case of HOL1045-1091. The continuation IH is
restricted by the literal source argument, lookup, nonzero clock, returned value,
and both shape guards of evaluate_ind. Callee evaluation needs no IH because
callee entry replaces the caller locals, giving identical runs. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_DecCall {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (bound : MlS) (shape : ShapeHOL)
    (function : MlS) (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (state : PanSemStateFiniteExact width σ)
    (continuationIH : ∀ args body callee returnShape retv (output : PanSemStateFiniteExact width σ),
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some args ∧
      lookupCodeHOLFinite state.code.lookup function args = some (body,callee,returnShape) ∧
      state.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned retv),output) ∧
      shapeOfHOLExact retv = shape ∧ shapeOfHOLExact retv = returnShape →
      ∀ result (post : PanSemStateFiniteExact width σ),
      name ∉ freeVarIdsHOL continuation ∧
      evaluateHOLFiniteState
        (setVarHOLFinite bound retv {output with locals := state.locals}) continuation = (result,post) →
      ∃ locals,
      evaluateHOLFiniteState
        {setVarHOLFinite bound retv {output with locals := state.locals} with
          locals := (setVarHOLFinite bound retv {output with locals := state.locals}).locals.updateEq (name,value)} continuation =
        (result,{post with locals := locals}) ∧
      (goodResHOL result = true ∧ result ≠ some .error → locals = post.locals.updateEq (name,value)))
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL (.decCall bound shape function arguments continuation) ∧
      evaluateHOLFiniteState state (.decCall bound shape function arguments continuation) = (res,post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name,value)}
        (.decCall bound shape function arguments continuation) = (res,{post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error → locals = post.locals.updateEq (name,value)) := by
  classical
  obtain ⟨hfresh,hev⟩ := h
  have hn : name ≠ bound := by
    intro he; apply hfresh; simp [freeVarIdsHOL, he]
  have hc : name ∉ freeVarIdsHOL continuation := by
    intro hm; apply hfresh; simp [freeVarIdsHOL, hm]
  have ha : name ∉ (arguments.map varExpHOL).flatten := by
    intro hm; apply hfresh; simp [freeVarIdsHOL, hm]
  have hargs := PanGlobalsFreshLocalEval.evalListFreshVar state arguments name value ha
  simp only [setVarEq] at hargs
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hev ⊢
  dsimp only at hev ⊢
  rw [hargs]
  cases haeval : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none =>
    simp only [haeval] at hev ⊢
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
    exact ⟨state.locals.updateEq (name,value),rfl,fun _ => rfl⟩
  | some args =>
    simp only [haeval] at hev ⊢
    cases hl : lookupCodeHOLFinite state.code.lookup function args with
    | none =>
      simp only [hl] at hev ⊢
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
      exact ⟨state.locals.updateEq (name,value),rfl,fun _ => rfl⟩
    | some triple =>
      obtain ⟨body,callee,returnShape⟩ := triple
      simp only [hl] at hev ⊢
      by_cases hclock : state.clock = 0
      · simp only [hclock,ite_true] at hev ⊢
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
        refine ⟨(emptyLocalsHOLFinite state).locals, ?_, ?_⟩
        · simp [emptyLocalsHOLFinite,hclock]
        · simp [goodResHOL]
      · simp only [hclock,ite_false] at hev ⊢
        have hentry : callEntryStateHOLFinite
            {state with locals := state.locals.updateEq (name,value)} callee =
            callEntryStateHOLFinite state callee := rfl
        rw [hentry]
        cases hb : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
        | mk result output =>
          simp only [hb] at hev ⊢
          cases result with
          | none =>
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
            exact ⟨output.locals,rfl,by simp⟩
          | some outcome =>
            cases outcome with
            | returned retv =>
              by_cases hs : (shapeEqHOL (shapeOfHOLExact retv) shape &&
                  shapeEqHOL (shapeOfHOLExact retv) returnShape) = true
              · simp only [hs,ite_true] at hev ⊢
                have hsh : shapeEqHOL (shapeOfHOLExact retv) shape = true ∧
                    shapeEqHOL (shapeOfHOLExact retv) returnShape = true := by
                  simpa only [Bool.and_eq_true] using hs
                have hshape : shapeOfHOLExact retv = shape := by
                  simpa only [shapeEqHOL_eq_true] using hsh.1
                have hreturnShape : shapeOfHOLExact retv = returnShape := by
                  simpa only [shapeEqHOL_eq_true] using hsh.2
                cases hcont : evaluateHOLFiniteState
                    (setVarHOLFinite bound retv {output with locals := state.locals}) continuation with
                | mk result final =>
                  obtain ⟨locals,hrun,hpost⟩ := continuationIH args body callee returnShape retv output
                    ⟨haeval,hl,hclock,hb,hshape,hreturnShape⟩ result final ⟨hc,hcont⟩
                  simp only [hcont] at hev
                  obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
                  simp only [setVarEq] at hrun ⊢
                  rw [updateCommute state.locals name bound value retv hn,hrun]
                  have hold : (state.locals.updateEq (name,value)).lookup bound = state.locals.lookup bound := by
                    simp [HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL,Ne.symm hn]
                  rw [hold]
                  refine ⟨HolFiniteMapExact.resVarEq locals (bound,state.locals.lookup bound),rfl,?_⟩
                  intro hg
                  rw [hpost hg]
                  exact restoreCommute final.locals name bound value (state.locals.lookup bound) hn
              · simp only [hs] at hev ⊢
                obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
                exact ⟨output.locals,rfl,by simp⟩
            | «break» | «continue» =>
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
              exact ⟨output.locals,rfl,by simp⟩
            | error | timeOut | exception eid exn | finalFfi outcome =>
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
              refine ⟨(emptyLocalsHOLFinite output).locals,rfl,?_⟩
              simp [goodResHOL]

end Flapjack.PanGlobalsFreshLocalDecCall
