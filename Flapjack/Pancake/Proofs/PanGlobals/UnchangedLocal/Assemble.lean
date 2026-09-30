import Flapjack.Pancake.Semantics.PanSem.EvaluateInd
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.Leaves
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.Dec
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.AssignPrimitive
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.ShMemLoad
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.ShMemStore
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.Seq
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.If
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.While
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.Results
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.TailCall
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.CallNoHandler
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.CallHandler
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.DecCall
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.ExtCall

namespace Flapjack.PanGlobalsUnchangedLocal
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.PanGlobalsUnchangedLocalWhile

/-- Canonical finite-state roundtrip re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Full original evaluate_unchanged_local1105-1135. All21 literal evaluate_ind
clauses are discharged internally; the original unused value binder is retained.
There is no public induction hypothesis or additional successful-run premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateUnchangedLocalHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (name : MlS) (_value : ValueHOL width) (program : ProgHOL width)
      (state : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
      (post : PanSemStateFiniteExact width σ),
      name ∉ freeVarIdsHOL program ∧ evaluateHOLFiniteState state program = (result,post) ∧
        goodResHOL result = true ∧ result ≠ some .error →
      post.locals.lookup name = state.locals.lookup name := by
  classical
  intro name value program state
  exact evaluateIndHOL (fun pair => unchangedLocalGoal name pair.1 pair.2) (by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro s; exact PanGlobalsUnchangedLocalLeaves.evaluateUnchangedLocal_Skip name value s
    · intro bound shape e body s ih
      exact PanGlobalsUnchangedLocalDec.evaluateUnchangedLocal_Dec name value bound shape e body s ih
    · intro kind bound e s
      exact PanGlobalsUnchangedLocalAssignPrimitive.evaluateUnchangedLocal_Assign name value kind bound e s
    · intro bound op es s
      exact PanGlobalsUnchangedLocalAssignPrimitive.evaluateUnchangedLocal_Primitive name value bound op es s
    · intro dst src s; exact PanGlobalsUnchangedLocalLeaves.evaluateUnchangedLocal_Store name value dst src s
    · intro dst src s; exact PanGlobalsUnchangedLocalLeaves.evaluateUnchangedLocal_Store32 name value dst src s
    · intro dst src s; exact PanGlobalsUnchangedLocalLeaves.evaluateUnchangedLocal_StoreByte name value dst src s
    · intro op kind bound ad s; exact PanGlobalsUnchangedLocalShMemLoad.evaluateUnchangedLocal_ShMemLoad name value op kind bound ad s
    · intro op ad e s; exact PanGlobalsUnchangedLocalShMemStore.evaluateUnchangedLocal_ShMemStore name value op ad e s
    · intro c1 c2 s ih; exact PanGlobalsUnchangedLocalSeq.evaluateUnchangedLocal_Seq name value c1 c2 s ih
    · intro e c1 c2 s ih; exact PanGlobalsUnchangedLocalIf.evaluateUnchangedLocal_If name value e c1 c2 s ih
    · intro s; exact PanGlobalsUnchangedLocalLeaves.evaluateUnchangedLocal_Break name value s
    · intro s; exact PanGlobalsUnchangedLocalLeaves.evaluateUnchangedLocal_Continue name value s
    · intro e c s ih; exact PanGlobalsUnchangedLocalWhile.evaluateUnchangedLocal_While name value e c s ih
    · intro e s; exact PanGlobalsUnchangedLocalResults.evaluateUnchangedLocal_Return name value e s
    · intro eid e s; exact PanGlobalsUnchangedLocalResults.evaluateUnchangedLocal_Raise name value eid e s
    · intro s; exact PanGlobalsUnchangedLocalLeaves.evaluateUnchangedLocal_Tick name value s
    · intro a b s; exact PanGlobalsUnchangedLocalLeaves.evaluateUnchangedLocal_Annot name value a b s
    · intro typ fname args s ⟨ihHandler,_ihBody⟩
      cases typ with
      | none => exact PanGlobalsUnchangedLocalTailCall.evaluateUnchangedLocal_CallNone name value fname args s
      | some typ =>
        rcases typ with ⟨target,handler⟩
        cases handler with
        | none => exact PanGlobalsUnchangedLocalCallNoHandler.evaluateUnchangedLocal_CallNoHandler name value target fname args s
        | some handler =>
          rcases handler with ⟨eid,evar,p⟩
          apply PanGlobalsUnchangedLocalCallHandler.evaluateUnchangedLocal_CallHandler name value target eid evar p fname args s
          intro actual body callee returnShape st sourceId exn sh ⟨ha,hl,hclock,hbody,heq,hesh,hshape,hvalid⟩
          exact ihHandler actual (body,callee,returnShape) body (callee,returnShape) callee returnShape
            (some (.exception sourceId exn),st) (some (.exception sourceId exn)) st (.exception sourceId exn) sourceId exn
            (target,some (eid,evar,p)) target (some (eid,evar,p)) (eid,evar,p) eid (evar,p) evar p sh
            ⟨ha,hl,rfl,rfl,hclock,hbody.symm,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,heq,hesh,hshape,hvalid⟩
    · intro bound shape fname args cont s ⟨ihCont,_ihBody⟩
      apply PanGlobalsUnchangedLocalDecCall.evaluateUnchangedLocal_DecCall name value bound shape fname args cont s
      intro actual body callee returnShape retv output ⟨ha,hl,hclock,hbody,hs,hrs⟩
      exact ihCont actual (body,callee,returnShape) body (callee,returnShape) callee returnShape
        (some (.returned retv),output) (some (.returned retv)) output (.returned retv) retv
        ⟨ha,hl,rfl,rfl,hclock,hbody.symm,rfl,rfl,rfl,hs,hrs⟩
    · intro f c cl a al s
      exact PanGlobalsUnchangedLocalExtCall.evaluateUnchangedLocal_ExtCall name value f c cl a al s)
    program state

end Flapjack.PanGlobalsUnchangedLocal
