import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.TailCall
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallNoDestination
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallLocal
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallHandlerNoDestination
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallLocalHandler
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallGlobal
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallGlobalHandler

namespace Flapjack.PanGlobalsCompileCorrectCall
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

open Flapjack.PanSemStateFiniteExact Flapjack.PanGlobalsCompileCorrect

/-- Complete Call conjunct of compile_correct, assembling the seven exhaustive
caltyp/destination/handler cases. Both IHs retain every binder and guard of the
original evaluate_ind Call conjunct; the motive is the original gen_goal,
including the existential target evaluation and complete post-state relation.
The bare newlocals entry qualifies the finite map bound inside those IHs. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals, newlocals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Call {width : Nat} {σ : Type} [NeZero width]
    (caltyp : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (fname : MlS) (argexps : List (ExpHOL width)) (s : PanSemStateFiniteExact width σ)
    (ihHandler : ∀ (args : List (ValueHOL width))
        (v7 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (prog : ProgHOL width) (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL)
        (eval_prog : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
        (v4 : Option (PanSemResultExact width)) (st : PanSemStateFiniteExact width σ)
        (v8 : PanSemResultExact width) (eid : MlS) (exn : ValueHOL width)
        (v : Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width))
        (v1 : Option (VarKind × MlS)) (v2 : Option (MlS × MlS × ProgHOL width))
        (v3 : MlS × MlS × ProgHOL width) (eid' : MlS) (v5 : MlS × ProgHOL width)
        (evar : MlS) (p : ProgHOL width) (sh : ShapeHOL),
      s.evalListHOLFinite
          (h := fun address => Classical.propDecidable (s.memaddrs address))
          argexps = some args ∧
        PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname args = some v7 ∧
        v7 = (prog, v12) ∧ v12 = (newlocals, return_sh) ∧ s.clock ≠ 0 ∧
        eval_prog = PanSemStateFiniteExact.evaluateHOLFiniteState
          { s.decClockHOLFinite with locals := newlocals } prog ∧
        eval_prog = (v4, st) ∧ v4 = some v8 ∧ v8 = .exception eid exn ∧
        caltyp = some v ∧ v = (v1, v2) ∧ v2 = some v3 ∧ v3 = (eid', v5) ∧
        v5 = (evar, p) ∧ eid = eid' ∧ s.eshapes.lookup eid = some sh ∧
        shapeOfHOLExact exn = sh ∧ isValidValueHOLExact s.toExact .local evar exn = true →
      compileCorrectGoal p (PanSemStateFiniteExact.setVarHOLFinite evar exn { st with locals := s.locals }))
    (ihCallee : ∀ (args : List (ValueHOL width))
        (v7 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (prog : ProgHOL width) (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL),
      s.evalListHOLFinite
          (h := fun address => Classical.propDecidable (s.memaddrs address))
          argexps = some args ∧
        PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname args = some v7 ∧
        v7 = (prog, v12) ∧ v12 = (newlocals, return_sh) ∧ s.clock ≠ 0 →
      compileCorrectGoal prog { s.decClockHOLFinite with locals := newlocals }) :
    compileCorrectGoal (.call caltyp fname argexps) s := by
  classical
  have calleeIH := fun args body callee returnShape (h :
      s.evalListHOLFinite (h := fun a => Classical.propDecidable (s.memaddrs a)) argexps = some args ∧
      lookupCodeHOLFinite s.code.lookup fname args = some (body,callee,returnShape) ∧ s.clock ≠ 0) =>
    ihCallee args (body,callee,returnShape) body (callee,returnShape) callee returnShape
      ⟨h.1,h.2.1,rfl,rfl,h.2.2⟩
  cases caltyp with
  | none =>
      exact PanGlobalsCompileCorrectTailCall.compileCorrect_CallNone s fname argexps calleeIH
  | some pair =>
      rcases pair with ⟨destination, handler⟩
      cases handler with
      | none =>
          cases destination with
          | none =>
              exact PanGlobalsCompileCorrectCallNoDestination.compileCorrect_CallNoDestination
                s fname argexps calleeIH
          | some pair =>
              rcases pair with ⟨kind,name⟩
              cases kind with
              | «local» =>
                  exact PanGlobalsCompileCorrectCallLocal.compileCorrect_CallLocal
                    s name fname argexps calleeIH
              | «global» =>
                  exact PanGlobalsCompileCorrectCallGlobal.compileCorrect_CallGlobal
                    s name fname argexps calleeIH
      | some triple =>
          rcases triple with ⟨handlerId,handlerVar,handlerBody⟩
          have handlerIH : ∀ args body callee returnShape value calleePost handlerShape,
              s.evalListHOLFinite (h := fun a => Classical.propDecidable (s.memaddrs a)) argexps = some args ∧
              lookupCodeHOLFinite s.code.lookup fname args = some (body,callee,returnShape) ∧
              s.clock ≠ 0 ∧
              evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
                (some (.exception handlerId value),calleePost) ∧
              s.eshapes.lookup handlerId = some handlerShape ∧
              shapeOfHOLExact value = handlerShape ∧
              isValidValueHOLExact s.toExact .local handlerVar value = true →
              compileCorrectGoal handlerBody
                (setVarHOLFinite handlerVar value {calleePost with locals := s.locals}) := by
            intro args body callee returnShape value calleePost handlerShape h
            exact ihHandler args (body,callee,returnShape) body (callee,returnShape)
              callee returnShape (some (.exception handlerId value),calleePost)
              (some (.exception handlerId value)) calleePost (.exception handlerId value)
              handlerId value (destination,some (handlerId,handlerVar,handlerBody))
              destination (some (handlerId,handlerVar,handlerBody))
              (handlerId,handlerVar,handlerBody) handlerId (handlerVar,handlerBody)
              handlerVar handlerBody handlerShape
              ⟨h.1,h.2.1,rfl,rfl,h.2.2.1,h.2.2.2.1.symm,rfl,rfl,rfl,
                rfl,rfl,rfl,rfl,rfl,rfl,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩
          cases destination with
          | none =>
              exact PanGlobalsCompileCorrectCallHandlerNoDestination.compileCorrect_CallHandlerNoDestination
                s fname argexps handlerId handlerVar handlerBody calleeIH handlerIH
          | some pair =>
              rcases pair with ⟨kind,name⟩
              cases kind with
              | «local» =>
                  apply PanGlobalsCompileCorrectCallLocalHandler.compileCorrect_CallLocalHandler
                    s name handlerId handlerVar handlerBody fname argexps calleeIH
                  intro args body callee returnShape postBody exceptionId value shape h
                  rcases h with ⟨ha,hl,hclock,hbody,rfl,hshape,hvalue,hvalid⟩
                  exact handlerIH args body callee returnShape value postBody shape
                    ⟨ha,hl,hclock,hbody,hshape,hvalue,hvalid⟩
              | «global» =>
                  exact PanGlobalsCompileCorrectCallGlobalHandler.compileCorrect_CallGlobalHandler
                    s name fname argexps handlerId handlerVar handlerBody calleeIH handlerIH

end Flapjack.PanGlobalsCompileCorrectCall
