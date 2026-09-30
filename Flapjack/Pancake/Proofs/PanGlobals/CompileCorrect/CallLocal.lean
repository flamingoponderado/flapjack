import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationClock
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationCode
import Flapjack.Pancake.Proofs.PanGlobals.OptMmapEvalCorrect
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsCompileCorrectCallLocal
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

/-- Genuine local-destination Call without handler case of compile_correct.
Only the original argument/lookup/nonzero-clock guarded callee IH is used.
Caller validity follows from the original locals equality; successful returns
restore those locals and use state_rel_set_var. No extra public premise.
The bare finite-map qualifier entry `callee` names the standalone map
universally bound inside the original callee IH. It is not an extra outer
map parameter or premise; the reviewed map translation applies at that binder. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals, callee])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_CallLocal {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (name : MlS) (function : MlS) (arguments : List (ExpHOL width))
    (ih : ∀ (args : List (ValueHOL width)) (body : ProgHOL width)
      (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL),
      evalListHOLFinite source (h := fun a => Classical.propDecidable (source.memaddrs a)) arguments = some args ∧
      lookupCodeHOLFinite source.code.lookup function args = some (body,callee,returnShape) ∧ source.clock ≠ 0 →
      compileCorrectGoal body (callEntryStateHOLFinite source callee)) :
    ∀ (res : Option (PanSemResultExact width)) (context : PanGlobalsContextExact width)
      (target post : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true context source target ∧
        evaluateHOLFiniteState source (.call (some (some (.local,name),none)) function arguments) = (res,post) ∧ res ≠ some .error →
      ∃ targetPost,
        evaluateHOLFiniteState target (compileProgExactHOL context (.call (some (some (.local,name),none)) function arguments)) = (res,targetPost) ∧
        panGlobalsStateRelHOLExact (goodResHOL res) context post targetPost := by
  classical
  intro res context target post ⟨hrel,hev,hne⟩
  have hcompile : compileProgExactHOL context (.call (some (some (.local,name),none)) function arguments : ProgHOL width) =
      .call (some (some (.local,name),none)) function (arguments.map (compileExpExactHOL context)) := by
    simp only [compileProgExactHOL,compileList_eq_map]
  rw [evaluateHOLFiniteState_call] at hev
  rw [hcompile,evaluateHOLFiniteState_call]
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
            by_cases hs : shapeEqHOL (shapeOfHOLExact value) returnShape = true
            · simp only [hs,↓reduceIte] at hev
              have hv : isValidValueHOLExact source.toExact .local name value =
                  isValidValueHOLExact target.toExact .local name value := by
                change (match source.locals.lookup name with
                  | some existing => shapeEqHOL (shapeOfHOLExact value) (shapeOfHOLExact existing)
                  | none => false) = _
                rw [hrel.2.1 rfl]
                rfl
              by_cases hvalid : isValidValueHOLExact source.toExact .local name value = true
              · have htvalid := hv ▸ hvalid
                simp only [hvalid,↓reduceIte] at hev
                obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
                obtain ⟨bt,hbt,hr⟩ := hbody (some (.returned value)) context (callEntryStateHOLFinite target callee) bs ⟨he,hb,by simp⟩
                have hrestore := (PanGlobalsStateRelationLocals.stateRelChangeLocalsHOL
                  context bs bt true source.locals).2 hr
                have hupdate := PanGlobalsStateRelationLocals.stateRelSetVarHOL context
                  { bs with locals := source.locals } { bt with locals := source.locals }
                  true name value hrestore
                refine ⟨setKvarHOLFinite .local name value { bt with locals := target.locals }, ?_, ?_⟩
                · simp only [hbt,hs,htvalid,↓reduceIte]
                · simpa only [setKvarHOLFinite,goodResHOL,hrel.2.1 rfl] using hupdate
              · simp only [if_neg hvalid] at hev
                exact False.elim (hne (Prod.mk.inj hev).1.symm)
            · simp only [if_neg hs] at hev
              exact False.elim (hne (Prod.mk.inj hev).1.symm)
          | exception eid value | timeOut | finalFfi outcome =>
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
            obtain ⟨bt,hbt,hr⟩ := hbody _ context (callEntryStateHOLFinite target callee) bs ⟨he,hb,by simp⟩
            exact ⟨emptyLocalsHOLFinite bt,by simp only [hbt],
              (PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL context bs bt false).2 hr⟩

end Flapjack.PanGlobalsCompileCorrectCallLocal
