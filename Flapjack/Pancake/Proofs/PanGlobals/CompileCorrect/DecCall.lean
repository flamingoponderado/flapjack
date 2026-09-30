import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.ResVar
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationClock
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationCode
import Flapjack.Pancake.Proofs.PanGlobals.OptMmapEvalCorrect
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsCompileCorrectDecCall
open Flapjack.Pancake.PanLang

/-- Canonical state roundtrips, re-exported for this relation theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip, re-exported for this relation theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

open Flapjack.PanSemStateFiniteExact

open Flapjack.PanGlobalsCompileCorrect

/-- Flapjack-only equation relating the literal recursive compiled argument list
    to the MAP spelling of OPT_MMAP_eval_correct; no separate HOL original. -/
private theorem compileList_eq_map {width : Nat} [NeZero width]
    (context : PanGlobalsContextExact width) (args : List (ExpHOL width)) :
    compileExpExactHOLList context args = args.map (compileExpExactHOL context) := by
  induction args with
  | nil => simp only [compileExpExactHOLList,List.map_nil]
  | cons e es ih => simp only [compileExpExactHOLList,List.map_cons,ih]

/-- Original compile_correct DecCall case (HOL1511-1533), with only the
original guarded callee and shape-matching continuation evaluate_ind IHs.
The continuation runs after restoring caller locals and binding the returned
value; its result restores the saved binding, whether present or absent.
Target evaluations and all entry/post relations are derived internally. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals, callee])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_DecCall {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (resultName : MlS) (shape : ShapeHOL)
    (function : MlS) (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (ih : ∀ (args : List (ValueHOL width)) (body : ProgHOL width)
      (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL),
      evalListHOLFinite source (h := fun a => Classical.propDecidable (source.memaddrs a)) arguments = some args ∧
      lookupCodeHOLFinite source.code.lookup function args = some (body,callee,returnShape) ∧ source.clock ≠ 0 →
      compileCorrectGoal body (callEntryStateHOLFinite source callee))
    (ihContinuation : ∀ (args : List (ValueHOL width)) (body : ProgHOL width)
      (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
      (value : ValueHOL width) (calleePost : PanSemStateFiniteExact width σ),
      evalListHOLFinite source (h := fun a => Classical.propDecidable (source.memaddrs a)) arguments = some args ∧
      lookupCodeHOLFinite source.code.lookup function args = some (body, callee, returnShape) ∧
      source.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body =
        (some (.returned value), calleePost) ∧
      shapeOfHOLExact value = shape ∧ shapeOfHOLExact value = returnShape →
      compileCorrectGoal continuation
        (setVarHOLFinite resultName value {calleePost with locals := source.locals})) :
    ∀ (res : Option (PanSemResultExact width)) (context : PanGlobalsContextExact width)
      (target post : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true context source target ∧
        evaluateHOLFiniteState source (.decCall resultName shape function arguments continuation) = (res,post) ∧ res ≠ some .error →
      ∃ targetPost,
        evaluateHOLFiniteState target (compileProgExactHOL context (.decCall resultName shape function arguments continuation)) = (res,targetPost) ∧
        panGlobalsStateRelHOLExact (goodResHOL res) context post targetPost := by
  classical
  intro res context target post ⟨hrel,hev,hne⟩
  have hcompile : compileProgExactHOL context (.decCall resultName shape function arguments continuation : ProgHOL width) =
      .decCall resultName shape function (arguments.map (compileExpExactHOL context))
        (compileProgExactHOL context continuation) := by
    simp only [compileProgExactHOL,compileList_eq_map]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hev
  rw [hcompile,evaluateHOLFiniteState_decCall_fixClockRewrite]
  cases ha : evalListHOLFinite source (h := fun a => Classical.propDecidable (source.memaddrs a)) arguments with
  | none => simp only [ha] at hev; exact False.elim (hne (Prod.mk.inj hev).1.symm)
  | some args =>
    simp only [ha] at hev
    have hta := PanGlobalsOptMmapEvalCorrect.optMmapEvalCorrectHOL context source target arguments args ⟨hrel,ha⟩
    simp only [hta]
    cases hl : lookupCodeHOLFinite source.code.lookup function args with
    | none => simp only [hl] at hev; exact False.elim (hne (Prod.mk.inj hev).1.symm)
    | some entry =>
      rcases entry with ⟨body,callee,returnShape⟩
      simp only [hl] at hev
      have htl := PanGlobalsStateRelationCode.stateRelLookupCodeHOL context source target true function args body callee returnShape ⟨hrel,hl⟩
      simp only [htl]
      have hc := hrel.2.2.2.2.2.1
      by_cases hz : source.clock = 0
      · have htz : target.clock = 0 := hc ▸ hz
        simp only [if_pos hz] at hev
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
        exact ⟨emptyLocalsHOLFinite target,by simp only [if_pos htz],
          (PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL context source target false).1 hrel⟩
      · have htz : target.clock ≠ 0 := hc ▸ hz
        simp only [if_neg hz] at hev
        simp only [if_neg htz]
        have hd := PanGlobalsStateRelationClock.stateRelDecClockHOL context source target true hrel
        have he := (PanGlobalsStateRelationLocals.stateRelChangeLocalsHOL context
          (decClockHOLFinite source) (decClockHOLFinite target) true callee).1 hd
        change panGlobalsStateRelHOLExact true context (callEntryStateHOLFinite source callee) (callEntryStateHOLFinite target callee) at he
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body with ⟨br,bs⟩
        simp only [hb] at hev
        have hbody := ih args body callee returnShape ⟨ha,hl,hz⟩
        cases br with
        | none => exact False.elim (hne (Prod.mk.inj hev).1.symm)
        | some result =>
          cases result with
          | «break» | «continue» | error => exact False.elim (hne (Prod.mk.inj hev).1.symm)
          | returned value =>
            by_cases hs : (shapeEqHOL (shapeOfHOLExact value) shape &&
                shapeEqHOL (shapeOfHOLExact value) returnShape) = true
            · simp only [if_pos hs] at hev
              rcases hk : evaluateHOLFiniteState
                (setVarHOLFinite resultName value {bs with locals := source.locals})
                continuation with ⟨cr, cs⟩
              simp only [hk] at hev
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
              obtain ⟨bt, hbt, hr⟩ := hbody (some (.returned value)) context
                (callEntryStateHOLFinite target callee) bs ⟨he, hb, by simp⟩
              have hlocals : source.locals = target.locals := hrel.2.1 rfl
              have hrestored := (PanGlobalsStateRelationLocals.stateRelChangeLocalsHOL
                context bs bt true source.locals).2 hr
              have hentry := PanGlobalsStateRelationLocals.stateRelSetVarHOL context
                {bs with locals := source.locals} {bt with locals := source.locals}
                true resultName value hrestored
              have hshapes := hs
              simp only [Bool.and_eq_true] at hshapes
              have hcontinuation := ihContinuation args body callee returnShape value bs
                ⟨ha, hl, hz, hb, (shapeEqHOL_eq_true _ _).mp hshapes.1,
                  (shapeEqHOL_eq_true _ _).mp hshapes.2⟩
              obtain ⟨ct, hct, hrc⟩ := hcontinuation cr context
                (setVarHOLFinite resultName value {bt with locals := target.locals}) cs
                ⟨by simpa only [hlocals] using hentry, hk, hne⟩
              refine ⟨{ct with locals := (HolFiniteMapExact.resVarEq ct.locals
                (resultName, target.locals.lookup resultName))}, ?_, ?_⟩
              · simp only [hbt, if_pos hs, hct]
              · exact PanGlobalsCompileCorrectResVar.stateRelResVar (goodResHOL cr)
                  context cs ct source target resultName resultName ⟨hrc, hrel⟩
            · simp only [if_neg hs] at hev
              exact False.elim (hne (Prod.mk.inj hev).1.symm)
          | exception eid value | timeOut | finalFfi outcome =>
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
            obtain ⟨bt,hbt,hr⟩ := hbody _ context (callEntryStateHOLFinite target callee) bs ⟨he,hb,by simp⟩
            exact ⟨emptyLocalsHOLFinite bt,by simp only [hbt],
              (PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL context bs bt false).2 hr⟩

end Flapjack.PanGlobalsCompileCorrectDecCall
