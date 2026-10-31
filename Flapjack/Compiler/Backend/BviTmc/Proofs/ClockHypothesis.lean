import Flapjack.Compiler.Backend.BviTmc.Proofs.ExtractedSimulation
import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateClockFull

/-! Smaller-clock induction hypotheses for TMC singleton simulations. -/
namespace Flapjack.Compiler.Backend.BviTmc.ClockHypothesis
open BviTmc BviSem BvlSem ListSimulation CallBlockAuxSimulation CallBlockSimulation

/-- Flapjack infrastructure: the ordinary, wrapper, and worker conclusions
for one expression, in the form consumed by the existing case proofs. -/
def SingletonPost {C F : Type} (e : Bvi.Exp) (source : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (loc : Nat) (result : BviResult) (final : BviState (Nat × C) F) : Prop :=
  Core [e] env2 f target result final ∧
  ∀ dest, optimisedCode loc dest source.code target.code →
    (∀ wrapper, rewriteWrapperSource loc dest env1.length e = some wrapper →
      Core [wrapper] env2 f target result final) ∧
    (opt = true → ∀ ptr c, holeHasVal f env1 env2 target.refs c → holeNotFinalised target.refs ptr →
      holEl env1.length env2 = .refPtr false ptr →
      IfWorker.WorkerCore (rewriteWorkerSource loc dest env1.length (env1.length + 1) env1.length e)
        env1 env2 f target ptr result final)

/-- Flapjack infrastructure: singleton simulations at strictly smaller
source clocks. The full lexicographic induction also handles same-clock
smaller expression lists and remains a separate obligation. -/
def SmallerClockIH {C F : Type} (clock : Nat) : Prop :=
  ∀ (e : Bvi.Exp) (source : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat) (loc : Nat)
    (result : BviResult) (final : BviState (Nat × C) F),
    source.clock < clock → evaluate [e] env1 source = (result, final) → noMutcons e →
    envRel opt f env1 env2 → stateRel f source target → result ≠ .err (.abort .typeError) →
    SingletonPost e source target env1 env2 opt f loc result final

/-- Flapjack infrastructure: a hypothesis for a larger clock also covers
every smaller clock bound. -/
theorem smallerClockIH_mono {C F : Type} (smaller larger : Nat) (bound : smaller ≤ larger)
    (ih : SmallerClockIH (C := C) (F := F) larger) : SmallerClockIH (C := C) (F := F) smaller := by
  intro e source target env1 env2 opt f loc result final clock run safe env states noError
  exact ih e source target env1 env2 opt f loc result final (by omega) run safe env states noError

private theorem decrement_related {C F : Type} (ticks : Nat) (f : HolFiniteMapExact Nat Nat)
    (source : BviState (Nat × C) F) (target : BviState C F) (states : stateRel f source target) :
    stateRel f (decClock (ticks + 1) source) (decClock (ticks + 1) target) := by
  simpa [BviSem.decClock, states.2.1] using stateRel_with_clock (source.clock - (ticks + 1)) f source target states

/-- Flapjack infrastructure: the global smaller-clock singleton hypothesis
supplies the ordinary call-block body hypothesis whenever the call can run. -/
theorem ordinary_body_from_smaller_clock {C F : Type} (loc : Nat) (source : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (f : HolFiniteMapExact Nat Nat)
    (states : stateRel f source target) (ih : SmallerClockIH (C := C) (F := F) source.clock) :
    OrdinaryBodyIH loc source target env1 env2 f := by
  intro ticks indices body body' args args' bodyResult bodyFinal wf clockBound sourceFound targetFound
    envRelated safe changed bodyRun notTypeError
  have smaller : (decClock (ticks + 1) source).clock < source.clock := by
    simp [BviSem.decClock]
    omega
  have decStates := decrement_related ticks f source target states
  have post := ih body (decClock (ticks + 1) source) (decClock (ticks + 1) target)
    args args' false f loc bodyResult bodyFinal smaller bodyRun safe envRelated decStates notTypeError
  by_cases same : body = body'
  · subst body'
    exact post.1
  · obtain ⟨workerLoc, code, rewrite⟩ := changed same
    exact (post.2 workerLoc code).1 body' rewrite

/-- Flapjack infrastructure: the global smaller-clock singleton hypothesis
also supplies the optimized worker-body hypothesis for each call block. -/
theorem worker_body_from_smaller_clock {C F : Type} (loc dest : Nat) (source : BviState (Nat × C) F)
    (env1 env2 : List Value) (f : HolFiniteMapExact Nat Nat)
    (ih : SmallerClockIH (C := C) (F := F) source.clock) : WorkerBodyIH loc dest source env1 env2 f := by
  intro ticks indices target ptr idx initial body worker bodyResult bodyFinal wf clockBound states code found
    bodyRun notTypeError safe rewrite envRelated hole notFinal
  have smaller : (decClock (ticks + 1) source).clock < source.clock := by
    simp [BviSem.decClock]
    omega
  have decStates := decrement_related ticks f source target states
  have post := ih body (decClock (ticks + 1) source) (decClock (ticks + 1) target)
    (indices.map (fun n => holEl n env1))
    (indices.map (fun n => holEl n env2) ++ [.refPtr false ptr, .number (Int.ofNat idx)])
    true f loc bodyResult bodyFinal smaller bodyRun safe envRelated decStates notTypeError
  have ptrAt : holEl (indices.map (fun n => holEl n env1)).length
      (indices.map (fun n => holEl n env2) ++ [.refPtr false ptr, .number (Int.ofNat idx)]) =
      .refPtr false ptr := by
    rw [holEl_eq_getElem _ _ (by simp)]
    simp [List.getElem_append_right]
  have work := (post.2 dest code).2 rfl ptr initial hole notFinal ptrAt
  simpa [rewrite] using work

/-- Flapjack infrastructure: all call-block simulation conclusions follow from
the singleton simulation at smaller clocks. Same-clock structural induction
and the full expression simulation are still separate obligations. -/
theorem evaluate_cb_from_smaller_clock {C F : Type} (loc : Nat) (cb : CallBlock)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [callBlockToBvi loc cb] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel opt f env1 env2)
    (states : stateRel f source target) (wf : wfBlock env1.length cb)
    (ih : SmallerClockIH (C := C) (F := F) source.clock) :
    Core [callBlockToBvi loc cb] env2 f target result final ∧
    ∀ dest, optimisedCode loc dest source.code target.code →
      (∀ tag left child right, cb = .callBlock tag left child right →
        Core [wrapperBlockSource tag left child right dest] env2 f target result final) ∧
      (∀ refs extras slot idx ptr, stateRefRel f source.refs refs →
        (∃ c, CallBlockEnvironment.allocHoleHasVal f refs extras slot idx c) →
        target.refs.domain ⊆ refs.domain → holEl slot extras = .refPtr false ptr →
        CallBlockAuxFrame.AuxCore cb dest env2 { target with refs := refs } f target.refs extras slot idx ptr result final) ∧
      (opt = true → ∀ ptr,
        (∃ c, holeHasVal f env1 env2 target.refs c) → holeNotFinalised target.refs ptr →
        holEl env1.length env2 = .refPtr false ptr →
        IfWorker.WorkerCore (workerBlockSource cb dest env1.length (env1.length + 1))
          env1 env2 f target ptr result final) := by
  exact evaluate_cb_simulation loc cb source target env1 env2 opt f result final run notTypeError environments
    states wf (ordinary_body_from_smaller_clock loc source target env1 env2 f states ih)
    (fun dest => worker_body_from_smaller_clock loc dest source env1 env2 f ih)

/-- Flapjack infrastructure: ordinary simulation of an extracted expression
from the binding-list induction and the smaller-clock singleton induction. -/
theorem evaluate_extracted_ordinary_from_smaller_clock {C F : Type} (loc : Nat) (cb : CallBlock)
    (e : Bvi.Exp) (bindings : List Bvi.Exp) (source : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult)
    (final : BviState (Nat × C) F) (run : evaluate [e] env1 source = (result, final))
    (extracted : toBlockSource env1.length loc e = some (bindings, cb))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel opt f env1 env2)
    (bindingsIH : ∀ r mid, evaluate bindings env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core bindings env2 f target r mid)
    (ih : SmallerClockIH (C := C) (F := F) source.clock) : Core [e] env2 f target result final := by
  apply ExtractedSimulation.evaluate_extracted_ordinary loc cb e bindings source target env1 env2 opt f result final
    run extracted notTypeError environments bindingsIH
  intro values values' mid g t sourceBindings targetBindings nextEnv states
  have clock := BviSem.evaluate_clock_le bindings env1 source
  rw [sourceBindings] at clock
  exact ordinary_body_from_smaller_clock loc mid t (values ++ env1) (values' ++ env2) g states
    (smallerClockIH_mono mid.clock source.clock clock ih)

/-- Flapjack infrastructure: wrapper simulation of an extracted constructor
from the binding-list induction and smaller-clock singleton induction. -/
theorem evaluate_extracted_wrapper_from_smaller_clock {C F : Type} (loc dest tag : Nat)
    (left right : List Nat) (child : CallBlock) (e : Bvi.Exp) (bindings : List Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [e] env1 source = (result, final))
    (extracted : toBlockSource env1.length loc e = some (bindings, .callBlock tag left child right))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel opt f env1 env2)
    (code : optimisedCode loc dest source.code target.code)
    (bindingsIH : ∀ r mid, evaluate bindings env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core bindings env2 f target r mid)
    (ih : SmallerClockIH (C := C) (F := F) source.clock) :
    Core [.let bindings (wrapperBlockSource tag left child right dest)] env2 f target result final := by
  apply ExtractedSimulation.evaluate_extracted_wrapper loc dest tag left right child e bindings source target env1 env2
    opt f result final run extracted notTypeError environments code bindingsIH
  intro values values' mid g t sourceBindings targetBindings nextEnv states nextCode
  have clock := BviSem.evaluate_clock_le bindings env1 source
  rw [sourceBindings] at clock
  exact worker_body_from_smaller_clock loc dest mid (values ++ env1) (values' ++ env2) g
    (smallerClockIH_mono mid.clock source.clock clock ih)

/-- Flapjack infrastructure: worker simulation of an extracted expression
from the binding-list induction and smaller-clock singleton induction. -/
theorem evaluate_extracted_worker_from_smaller_clock {C F : Type} (loc dest ptr : Nat) (cb : CallBlock)
    (e : Bvi.Exp) (bindings : List Bvi.Exp) (source : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 : List Value) (f : HolFiniteMapExact Nat Nat) (initial : Value)
    (result : BviResult) (final : BviState (Nat × C) F) (run : evaluate [e] env1 source = (result, final))
    (extracted : toBlockSource env1.length loc e = some (bindings, cb))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel true f env1 env2)
    (hole : holeHasVal f env1 env2 target.refs initial) (notFinal : holeNotFinalised target.refs ptr)
    (pointer : holEl env1.length env2 = .refPtr false ptr) (code : optimisedCode loc dest source.code target.code)
    (bindingsIH : ∀ r mid, evaluate bindings env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core bindings env2 f target r mid)
    (ih : SmallerClockIH (C := C) (F := F) source.clock) :
    IfWorker.WorkerCore (.let bindings (workerBlockSource cb dest (bindings.length + env1.length)
      (bindings.length + env1.length + 1))) env1 env2 f target ptr result final := by
  apply ExtractedSimulation.evaluate_extracted_worker loc dest ptr cb e bindings source target env1 env2 f initial
    result final run extracted notTypeError environments hole notFinal pointer code bindingsIH
  intro values values' mid g t sourceBindings blockRun nextEnv states nextCode
  have clock := BviSem.evaluate_clock_le bindings env1 source
  rw [sourceBindings] at clock
  exact worker_body_from_smaller_clock loc dest mid (values ++ env1) (values' ++ env2) g
    (smallerClockIH_mono mid.clock source.clock clock ih)

/-- Flapjack infrastructure: the extracted-expression singleton case follows
from the binding-list induction and the smaller-clock singleton induction.
The full lexicographic induction and source safety/size obligations are
still separate. -/
theorem evaluate_extracted_from_smaller_clock {C F : Type} (loc : Nat) (cb : CallBlock)
    (e : Bvi.Exp) (bindings : List Bvi.Exp) (source : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult)
    (final : BviState (Nat × C) F) (run : evaluate [e] env1 source = (result, final))
    (extracted : toBlockSource env1.length loc e = some (bindings, cb))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel opt f env1 env2)
    (bindingsIH : ∀ r mid, evaluate bindings env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core bindings env2 f target r mid)
    (ih : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost e source target env1 env2 opt f loc result final := by
  refine ⟨evaluate_extracted_ordinary_from_smaller_clock loc cb e bindings source target env1 env2 opt f result final
    run extracted notTypeError environments bindingsIH ih, ?_⟩
  intro dest code
  constructor
  · intro wrapper wrapperRun
    rcases toBlock_cases env1.length loc e bindings cb extracted with
      ⟨tag, args, left, child, right, shape, cbShape⟩ | ⟨ticks, args, vars, shape, cbShape⟩
    · subst cb
      have wrapperEq := ExtractedSimulation.rewrite_wrapper_extracted loc dest env1.length tag e bindings left right child extracted
      rw [wrapperEq] at wrapperRun
      cases wrapperRun
      exact evaluate_extracted_wrapper_from_smaller_clock loc dest tag left right child e bindings source target
        env1 env2 opt f result final run extracted notTypeError environments code bindingsIH ih
    · subst e
      simp [rewriteWrapperSource] at wrapperRun
  · intro optTrue ptr initial hole notFinal pointer
    have trueEnv : envRel true f env1 env2 := by simpa [optTrue] using environments
    have worker := evaluate_extracted_worker_from_smaller_clock loc dest ptr cb e bindings source target env1 env2 f initial
      result final run extracted notTypeError trueEnv hole notFinal pointer code bindingsIH ih
    rw [ExtractedSimulation.rewrite_worker_extracted loc dest env1.length e bindings cb extracted]
    exact worker

end Flapjack.Compiler.Backend.BviTmc.ClockHypothesis
