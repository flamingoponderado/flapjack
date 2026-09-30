import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Dec
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Assign
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Primitive
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Store
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.FixedStores
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.ShMemLoad
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.ShMemStore
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Seq
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.If
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.While
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.ReturnRaise
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.ClockAnnot
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Call
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.DecCall
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.ExtCall
import Flapjack.Pancake.Semantics.PanSem.EvaluateInd

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace FpermAssemblySupport
/-- Canonical representation roundtrip, with no independent HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermAssemblySupport

/-- Full source function-permutation theorem. Faithful evaluator induction
derives every recursive IH internally, including both While backedges, callees
and handlers. The sole premise is the original source run; every result and
complete post-state is preserved apart from the specified code permutation. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFpermHOL {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (program : ProgHOL width) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state program = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g program) = (res, { post with code := fpermCodeHOL f g post.code }) := by
  classical
  have cases : PanEvaluateIndHyps
      (fun pair : ProgHOL width × PanSemStateFiniteExact width σ =>
        fpermEvaluateGoal f g pair.1 pair.2) := by
    unfold PanEvaluateIndHyps
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact evaluateFperm_Skip f g
    · intro name shape initializer body source ih
      exact evaluateFperm_Dec f g name shape initializer body source ih
    · intro kind name expression source
      exact evaluateFperm_Assign f g source kind name expression
    · intro name operator arguments source
      exact evaluateFperm_Primitive f g source name operator arguments
    · intro address value source
      exact evaluateFperm_Store f g source address value
    · intro address value source
      exact evaluateFperm_Store32 f g source address value
    · intro address value source
      exact evaluateFperm_StoreByte f g source address value
    · intro operator kind name address source
      exact evaluateFperm_ShMemLoad f g source operator kind name address
    · intro operator address value source
      exact evaluateFperm_ShMemStore f g source operator address value
    · intro first second source ⟨ihSecond, ihFirst⟩
      exact evaluateFperm_Seq f g first second source ihSecond ihFirst
    · intro condition first second source ih
      exact evaluateFperm_If f g condition first second source ih
    · exact evaluateFperm_Break f g
    · exact evaluateFperm_Continue f g
    · intro condition body source ⟨ihContinue, ihNone, ihBody⟩
      exact evaluateFperm_While f g condition body source ihContinue ihNone ihBody
    · intro expression source
      exact evaluateFperm_Return f g source expression
    · intro exception expression source
      exact evaluateFperm_Raise f g source exception expression
    · exact evaluateFperm_Tick f g
    · intro tag text source
      exact evaluateFperm_Annot f g source tag text
    · intro info name arguments source ⟨ihHandler, ihCallee⟩
      apply evaluateFperm_Call f g source info name arguments
      · intro values body callee shape guards
        exact ihCallee values (body,callee,shape) body (callee,shape) callee shape
          ⟨guards.1,guards.2.1,rfl,rfl,guards.2.2⟩
      · intro values body callee returnShape output destination eid evar handler value shape guards
        exact ihHandler values (body,callee,returnShape) body (callee,returnShape)
          callee returnShape (some (.exception eid value),output)
          (some (.exception eid value)) output (.exception eid value) eid value
          (destination,some (eid,evar,handler)) destination (some (eid,evar,handler))
          (eid,evar,handler) eid (evar,handler) evar handler shape
          ⟨guards.1,guards.2.1,rfl,rfl,guards.2.2.1,
            guards.2.2.2.1.symm,rfl,rfl,rfl,guards.2.2.2.2.1,
            rfl,rfl,rfl,rfl,rfl,guards.2.2.2.2.2.1,
            guards.2.2.2.2.2.2.1,guards.2.2.2.2.2.2.2⟩
    · intro name shape function arguments continuation source ⟨ihContinuation, ihCallee⟩
      apply evaluateFperm_DecCall f g name shape function arguments continuation source
      · intro values body callee returnShape guards
        exact ihCallee values (body,callee,returnShape) body (callee,returnShape)
          callee returnShape ⟨guards.1,guards.2.1,rfl,rfl,guards.2.2⟩
      · intro values body callee returnShape value output guards
        exact ihContinuation values (body,callee,returnShape) body (callee,returnShape)
          callee returnShape (some (.returned value),output) (some (.returned value))
          output (.returned value) value
          ⟨guards.1,guards.2.1,rfl,rfl,guards.2.2.1,
            guards.2.2.2.1.symm,rfl,rfl,rfl,guards.2.2.2.2.1,guards.2.2.2.2.2⟩
    · intro function configuration configurationLength array arrayLength source
      exact evaluateFperm_ExtCall f g source function configuration configurationLength array arrayLength
  exact evaluateIndHOL
    (fun pair : ProgHOL width × PanSemStateFiniteExact width σ =>
      fpermEvaluateGoal f g pair.1 pair.2) cases program state res post heval

end Flapjack

