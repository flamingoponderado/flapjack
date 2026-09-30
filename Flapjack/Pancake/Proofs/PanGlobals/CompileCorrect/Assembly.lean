import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Dec
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.AssignLocal
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.AssignGlobal
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Primitive
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Store
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Store32
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.StoreByte
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.ShMemGlobal
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Seq
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.If
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.While
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Return
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Raise
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Call
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.DecCall
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.ExtCall
import Flapjack.Pancake.Semantics.PanSem.EvaluateInd

namespace Flapjack.PanGlobalsCompileCorrectAssembly
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

/-- Complete original compile_correct theorem. The faithful evaluate_ind supplies
all recursive IHs internally. The public statement retains exactly gen_goal:
a related initial state, the source run and non-Error result imply an actual
compiled target run with the same result and complete good_res state relation.
All 21 constructors use accepted case proofs; no public IH or target-run premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectHOL {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (source : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (context : PanGlobalsContextExact width)
    (target post : PanSemStateFiniteExact width σ)
    (h : panGlobalsStateRelHOLExact true context source target ∧
      evaluateHOLFiniteState source program = (res,post) ∧ res ≠ some .error) :
    ∃ targetPost,
      evaluateHOLFiniteState target (compileProgExactHOL context program) = (res,targetPost) ∧
      panGlobalsStateRelHOLExact (goodResHOL res) context post targetPost := by
  classical
  have cases : PanEvaluateIndHyps
      (fun pair : ProgHOL width × PanSemStateFiniteExact width σ =>
        compileCorrectGoal pair.1 pair.2) := by
    unfold PanEvaluateIndHyps
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact compileCorrect_Skip
    · intro name shape initializer body state ih
      apply PanGlobalsCompileCorrectDec.compileCorrect_Dec name shape initializer body state
      intro value hv
      exact ih value hv
    · intro kind name expression state
      cases kind with
      | «local» => exact PanGlobalsCompileCorrectAssignLocal.compileCorrect_AssignLocal state name expression
      | «global» => exact PanGlobalsCompileCorrectAssignGlobal.compileCorrect_AssignGlobal state name expression
    · intro name operator arguments state
      exact PanGlobalsCompileCorrectPrimitive.compileCorrect_Primitive state name operator arguments
    · exact PanGlobalsCompileCorrectStore.compileCorrect_Store
    · exact PanGlobalsCompileCorrectStore32.compileCorrect_Store32
    · exact PanGlobalsCompileCorrectStoreByte.compileCorrect_StoreByte
    · exact compileCorrect_ShMemLoad
    · exact compileCorrect_ShMemStore
    · exact compileCorrect_Seq
    · intro condition thenBranch elseBranch state ih
      exact PanGlobalsCompileCorrectIf.compileCorrect_If condition thenBranch elseBranch state ih
    · exact compileCorrect_Break
    · exact compileCorrect_Continue
    · intro condition body state ⟨ihContinue,ihNone,ihBody⟩
      apply PanGlobalsCompileCorrectWhile.compileCorrect_While state condition body
      · intro word postBody guards
        exact ihContinue (.val (.word word)) (.word word) word (some .continue)
          postBody .continue
          ⟨guards.1,rfl,rfl,guards.2.1,guards.2.2.1,guards.2.2.2,rfl,rfl⟩
      · intro word postBody guards
        exact ihNone (.val (.word word)) (.word word) word none postBody
          ⟨guards.1,rfl,rfl,guards.2.1,guards.2.2.1,guards.2.2.2,rfl⟩
      · intro word guards
        exact ihBody (.val (.word word)) (.word word) word
          ⟨guards.1,rfl,rfl,guards.2.1,guards.2.2⟩
    · exact PanGlobalsCompileCorrectReturn.compileCorrect_Return
    · intro eid expression state
      exact PanGlobalsCompileCorrectRaise.compileCorrect_Raise state eid expression
    · exact compileCorrect_Tick
    · intro tag text state
      exact compileCorrect_Annot state tag text
    · intro caltyp fname arguments state ⟨ihHandler,ihCallee⟩
      exact PanGlobalsCompileCorrectCall.compileCorrect_Call caltyp fname arguments state ihHandler ihCallee
    · intro resultName shape fname arguments continuation state ⟨ihContinuation,ihCallee⟩
      apply PanGlobalsCompileCorrectDecCall.compileCorrect_DecCall
        state resultName shape fname arguments continuation
      · intro args body callee returnShape guards
        exact ihCallee args (body,callee,returnShape) body (callee,returnShape)
          callee returnShape ⟨guards.1,guards.2.1,rfl,rfl,guards.2.2⟩
      · intro args body callee returnShape value postBody guards
        exact ihContinuation args (body,callee,returnShape) body (callee,returnShape)
          callee returnShape (some (.returned value),postBody) (some (.returned value))
          postBody (.returned value) value
          ⟨guards.1,guards.2.1,rfl,rfl,guards.2.2.1,
            guards.2.2.2.1.symm,rfl,rfl,rfl,guards.2.2.2.2.1,guards.2.2.2.2.2⟩
    · intro function configuration configurationLength array arrayLength state
      exact PanGlobalsCompileCorrectExtCall.compileCorrect_ExtCall
        state function configuration configurationLength array arrayLength
  exact evaluateIndHOL
    (fun pair : ProgHOL width × PanSemStateFiniteExact width σ =>
      compileCorrectGoal pair.1 pair.2) cases program source res context target post h

end Flapjack.PanGlobalsCompileCorrectAssembly
