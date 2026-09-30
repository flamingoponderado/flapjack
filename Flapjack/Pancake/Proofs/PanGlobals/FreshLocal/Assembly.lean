import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Leaves
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Dec
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Assign
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Primitive
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Memory
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.ShMemLoad
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.ShMemStore
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Seq
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.If
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.While
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Results
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.TailCall
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.CallNoHandler
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.CallHandler
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.DecCall
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.ExtCall
import Flapjack.Pancake.Semantics.PanSem.EvaluateInd

namespace Flapjack.PanGlobalsFreshLocalAssembly
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.PanGlobalsFreshLocalIf

/-- Canonical finite-state roundtrip re-export, with no standalone HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Local equality of canonical update interfaces; no standalone HOL original. -/
private theorem updateEq_eq_update {width : Nat} [NeZero width]
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (entry : MlS × ValueHOL width) :
    locals.updateEq entry = locals.update entry := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.lookup_updateEq, HolFiniteMapExact.lookup_update,
    FUPDATE_HOL_eq_FUPDATE]

/-- Full evaluate_fresh_local, assembled by the literal evaluate_ind principle.
All recursive hypotheses are discharged internally. The public statement retains
HOL's nonfree/source-run premise, existential locals, and good_res/non-Error
conditional post-update, with no additional hypothesis. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocalHOL {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (program : ProgHOL width)
    (state : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : name ∉ freeVarIdsHOL program ∧ evaluateHOLFiniteState state program = (result, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)} program =
        (result, {post with locals := locals}) ∧
      (goodResHOL result = true ∧ result ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  classical
  have hall : ∀ (p : ProgHOL width) (s : PanSemStateFiniteExact width σ), freshLocalGoal name value p s := by
    apply evaluateIndHOL (fun ps => freshLocalGoal name value ps.1 ps.2)
    repeat' apply And.intro
    · intro s
      exact PanGlobalsFreshLocal.evaluateFreshLocal_Skip name value s
    · intro bound shape init body s ih r st hh
      apply PanGlobalsFreshLocalDec.evaluateFreshLocal_Dec name value bound shape init body s ?_ r st hh
      intro initValue hg
      simpa only [freshLocalGoal, updateEq_eq_update] using ih initValue hg
    · intro kind dest src s
      exact PanGlobalsFreshLocalAssign.evaluateFreshLocal_Assign name value kind dest src s
    · intro dest op args s
      exact PanGlobalsFreshLocalPrimitive.evaluateFreshLocal_Primitive name value dest op args s
    · intro dst src s
      exact PanGlobalsFreshLocalMemory.evaluateFreshLocal_Store name value dst src s
    · intro dst src s
      exact PanGlobalsFreshLocalMemory.evaluateFreshLocal_Store32 name value dst src s
    · intro dst src s
      exact PanGlobalsFreshLocalMemory.evaluateFreshLocal_StoreByte name value dst src s
    · intro op kind dest ad s
      exact PanGlobalsFreshLocalShMemLoad.evaluateFreshLocal_ShMemLoad name value op kind dest ad s
    · intro op ad src s
      exact PanGlobalsFreshLocalShMemStore.evaluateFreshLocal_ShMemStore name value op ad src s
    · intro first second s ih
      exact PanGlobalsFreshLocalSeq.evaluateFreshLocal_Seq name value first second s ih
    · intro e first second s ih
      exact PanGlobalsFreshLocalIf.evaluateFreshLocal_If name value e first second s ih
    · intro s
      exact PanGlobalsFreshLocal.evaluateFreshLocal_Break name value s
    · intro s
      exact PanGlobalsFreshLocal.evaluateFreshLocal_Continue name value s
    · intro e body s ih r st hh
      apply PanGlobalsFreshLocalWhile.evaluateFreshLocal_While name value e body s ?_ ?_ ?_ r st hh
      · exact ih.1
      · exact ih.2.1
      · exact ih.2.2
    · intro e s
      exact PanGlobalsFreshLocalResults.evaluateFreshLocal_Return name value e s
    · intro eid e s
      exact PanGlobalsFreshLocalResults.evaluateFreshLocal_Raise name value eid e s
    · intro s
      exact PanGlobalsFreshLocal.evaluateFreshLocal_Tick name value s
    · intro a b s
      exact PanGlobalsFreshLocal.evaluateFreshLocal_Annot name value a b s
    · intro info function args s ih r st hh
      cases info with
      | none => exact PanGlobalsFreshLocalTailCall.evaluateFreshLocal_CallNone name value function args s r st hh
      | some info =>
        obtain ⟨target, handler⟩ := info
        cases handler with
        | none => exact PanGlobalsFreshLocalCallNoHandler.evaluateFreshLocal_CallNoHandler name value target function args s r st hh
        | some handler =>
          obtain ⟨eid, evar, p⟩ := handler
          apply PanGlobalsFreshLocalCallHandler.evaluateFreshLocal_CallHandler name value target eid evar p function args s ?_ r st hh
          intro values body callee sh output exid exn exshape hg
          exact ih.1 values (body,callee,sh) body (callee,sh) callee sh
            (some (.exception exid exn),output) (some (.exception exid exn)) output
            (.exception exid exn) exid exn (target,some (eid,evar,p)) target
            (some (eid,evar,p)) (eid,evar,p) eid (evar,p) evar p exshape
            ⟨hg.1,hg.2.1,rfl,rfl,hg.2.2.1,hg.2.2.2.1.symm,rfl,rfl,rfl,
              rfl,rfl,rfl,rfl,rfl,hg.2.2.2.2.1,hg.2.2.2.2.2.1,
              hg.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2⟩
    · intro bound shape function args continuation s ih r st hh
      apply PanGlobalsFreshLocalDecCall.evaluateFreshLocal_DecCall name value bound shape function args continuation s ?_ r st hh
      intro values body callee rshape ret output hg
      exact ih.1 values (body,callee,rshape) body (callee,rshape) callee rshape
        (some (.returned ret),output) (some (.returned ret)) output (.returned ret) ret
        ⟨hg.1,hg.2.1,rfl,rfl,hg.2.2.1,hg.2.2.2.1.symm,rfl,rfl,rfl,
          hg.2.2.2.2.1,hg.2.2.2.2.2⟩
    · intro index p1 l1 p2 l2 s
      exact PanGlobalsFreshLocalExtCall.evaluateFreshLocal_ExtCall name value index p1 l1 p2 l2 s
  exact hall program state result post h

end Flapjack.PanGlobalsFreshLocalAssembly
