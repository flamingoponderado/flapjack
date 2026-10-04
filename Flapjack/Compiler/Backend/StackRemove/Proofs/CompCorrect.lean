import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CallReturnHandler
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.FFI
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StoreTransfers
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CallReturnNone
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Bitmap
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Install
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.DataBufferWrite
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Atoms
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.RawCall
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CallTail
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StoreConsts
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StackMemoryAny
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.JumpLower
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.If
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Locations
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Control
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.ShMemOp
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StackSpace
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Loop
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.HeapOperation
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StackMemory
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Instructions
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CodeBufferWrite
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Call
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StackSize
namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.Assembly
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps StackSemControl StackSemMeasure
/-- Flapjack-only normalization of the case proofs' dependent result matches.
It retains the actual target run and selects the identical original result
postcondition constructor by constructor; no independent HOL declaration. -/
local macro "normalize_result" r:ident "using" proof:term : tactic =>
  `(tactic| (
    rcases ($proof:term) with ⟨clock, post, run, relation⟩
    refine ⟨clock, post, run, ?_⟩
    cases $r:ident with
    | none => exact relation
    | some returned => cases returned <;> exact relation))

/-- Flapjack-only induction infrastructure on the exact evaluator's original
clock-first lexicographic measure. Every recursive premise is discharged at
its actual source call site, using its source guard and clock law. -/
private theorem correctnessMeasure {width : Nat} [NeZero width] {C F : Type} :
    ∀ (measure : Nat × Nat) (program : HolProg width) (source : StackSemStateFiniteExact width C F),
      stackSemMeasure program source = measure →
      ∀ (result : Option (StackSemResult width)) (postSource target : StackSemStateFiniteExact width C F)
        (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool),
      ∀ (_hypothesis : evaluate (program, source) = (result, postSource) ∧ result ≠ some .error ∧
        stateRelHOL jump bounds pointer source target ∧ StackProps.regBound program pointer),
      ∃ clock postTarget,
        evaluate (comp jump bounds pointer program, {target with clock := clock + target.clock}) =
          (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  intro measure
  induction measure using Compiler.Backend.StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro program source hm result postSource target pointer bounds jump hypothesis
  subst hm
  cases program
  all_goals first
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.FFI.compCorrectFFI _ _ _ _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.StoreTransfers.compCorrectGet _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.StoreTransfers.compCorrectSet _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.Bitmap.compCorrectBitmapLoad _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.Install.compCorrectInstall _ _ _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.DataBufferWrite.compCorrectDataBufferWrite _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.compCorrectSkip _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.compCorrectHalt _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.compCorrectAlloc _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.StoreConsts.compCorrectStoreConsts _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackMemoryAny.compCorrectStackLoadAny _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackMemoryAny.compCorrectStackStoreAny _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.Locations.compCorrectLocValue _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.Control.compCorrectTick _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.Control.compCorrectReturn _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.Control.compCorrectRaise _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.Control.compCorrectBreak _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.Control.compCorrectContinue _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.ShMemOp.compCorrectShMemOp _ _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackSpace.compCorrectStackFree _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackSpace.compCorrectStackAlloc _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.HeapOperation.compCorrectOpCurrHeap _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackMemory.compCorrectStackLoad _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackMemory.compCorrectStackStore _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.Instructions.compCorrectInst _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.CodeBufferWrite.compCorrectCodeBufferWrite _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackSize.compCorrectStackGetSize _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackSize.compCorrectStackSetSize _ _ _ _ _ _ _ _ hypothesis))
    | skip
  case seq first second =>
    refine (by normalize_result result using (Seq.compCorrectSeq first second source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro r post t k off j h
      normalize_result r using (ih _ (seq_first_measure_lt first second source) first source rfl r post t k off j h)
    · intro middle firstRun
      have smaller := seq_second_measure_lt first second source ((none : Option (StackSemResult width)), middle)
      have unclamped := StackSemEvaluateClock.fixClockEvaluate first source
      rw [firstRun] at unclamped
      rw [unclamped] at smaller
      intro r post t k off j h
      normalize_result r using (ih _ smaller second middle rfl r post t k off j h)
  case ite comparison register operand first second =>
    refine (by normalize_result result using (If.compCorrectIf comparison register operand first second source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro left right _ _ _ r post t k off j h
      normalize_result r using (ih _ (if_first_measure_lt comparison register operand first second source) first source rfl r post t k off j h)
    · intro left right _ _ _ r post t k off j h
      normalize_result r using (ih _ (if_second_measure_lt comparison register operand first second source) second source rfl r post t k off j h)
  case loop body =>
    refine (by normalize_result result using (Loop.compCorrectLoop body source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro r post t k off j h
      normalize_result r using (ih _ (loop_body_measure_lt body source) body source rfl r post t k off j h)
    · intro bodyResult middle bodyRun _ nonzero
      have unclamped := StackSemEvaluateClock.fixClockEvaluate body source
      rw [bodyRun] at unclamped
      have smaller := loop_reentry_measure_lt body source (bodyResult, middle)
        (by simpa only [unclamped] using nonzero)
      rw [unclamped] at smaller
      intro r post t k off j h
      normalize_result r using (ih _ smaller (.loop body) (decClock middle) rfl r post t k off j h)
  case jumpLower first second label =>
    refine (by normalize_result result using (JumpLower.compCorrectJumpLower first second label source result postSource target pointer bounds jump ?_ hypothesis))
    · intro left right program _ _ _ _ nonzero r post t k off j h
      normalize_result r using (ih _ (callee_measure_lt program (.jumpLower first second label) source nonzero) program (decClock source) rfl r post t k off j h)
  case rawCall label =>
    refine (by normalize_result result using (RawCall.compCorrectRawCall label source result postSource target pointer bounds jump ?_ hypothesis))
    · intro frame body _ nonzero r post t k off j h
      normalize_result r using (ih _ (callee_measure_lt body (.rawCall label) source nonzero) body (decClock source) rfl r post t k off j h)
  case call ret dest handler =>
    refine (by normalize_result result using (CallAssembly.compCorrectCall ret dest handler source result postSource target pointer bounds jump ?_ ?_ ?_ hypothesis))
    · cases ret with
      | none =>
        intro program _ _ nonzero r post t k off j h
        normalize_result r using (ih _ (callee_measure_lt program (.call none dest handler) source nonzero) program (decClock source) rfl r post t k off j h)
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        intro program _ nonzero
        have smaller := callee_measure_lt program (.call (some (body, link, l1, l2)) dest handler)
          (setVar link (.loc l1 l2) source) nonzero
        intro r post t k off j h
        normalize_result r using (ih _ smaller program (decClock (setVar link (.loc l1 l2) source)) rfl r post t k off j h)
    · cases ret with
      | none => trivial
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        intro program middle _ nonzero calleeRun
        have unclamped := StackSemEvaluateClock.fixClockEvaluate program (decClock (setVar link (.loc l1 l2) source))
        rw [calleeRun] at unclamped
        have smaller := call_continuation_measure_lt body (.call (some (body, link, l1, l2)) dest handler)
          source link l1 l2 ((some (.result (.loc l1 l2)) : Option (StackSemResult width)), middle) nonzero
        rw [unclamped] at smaller
        intro r post t k off j h
        normalize_result r using (ih _ smaller body middle rfl r post t k off j h)
    · cases ret with
      | none => trivial
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        cases handler with
        | none => trivial
        | some handlerEntry =>
          rcases handlerEntry with ⟨handlerBody, hl1, hl2⟩
          intro program middle _ nonzero calleeRun
          have unclamped := StackSemEvaluateClock.fixClockEvaluate program (decClock (setVar link (.loc l1 l2) source))
          rw [calleeRun] at unclamped
          have smaller := call_continuation_measure_lt handlerBody
            (.call (some (body, link, l1, l2)) dest (some (handlerBody, hl1, hl2)))
            source link l1 l2 ((some (.exception (.loc hl1 hl2)) : Option (StackSemResult width)), middle) nonzero
          rw [unclamped] at smaller
          intro r post t k off j h
          normalize_result r using (ih _ smaller handlerBody middle rfl r post t k off j h)

/-- Canonical codec of the actual imported evaluator state. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original StackRemove `comp_correct` (1481–1493). The faithful
source evaluation, non-Error result, entire state relation and register
bound are its only four premises. Well-founded induction on the evaluator's
original measure derives every guarded recursive call and assembles all 34
native constructor simulations. The compiled evaluation and extra clock,
and the full original result-dispatch postcondition, are conclusions.
The native evaluator closure inherits the reviewed reals_as_rational_cuts
FP carrier (SOUNDNESS item 8), with no additional semantic assumptions. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrect {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (program, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound program pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer program,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  normalize_result result using (correctnessMeasure (stackSemMeasure program source)
    program source rfl result postSource target pointer bounds jump hypothesis)

end Flapjack.Compiler.Backend.StackRemove.CompCorrect.Assembly
