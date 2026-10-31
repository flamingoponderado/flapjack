import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockWorkerSimulation

/-! Assembled call-block simulation conclusions. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallBlockSimulation
open BviTmc BviSem BvlSem CallBlockAuxFrame CallBlockAuxSimulation

/-- Flapjack infrastructure: the smaller-clock ordinary function-body
simulation used by recursive call-block leaves. -/
def OrdinaryBodyIH {C F : Type} (loc : Nat) (source : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (f : HolFiniteMapExact Nat Nat) : Prop :=
  ∀ ticks indices body body' args args' bodyResult bodyFinal,
    wfVars env1.length indices →
    findCode (some loc) (indices.map (fun n => holEl n env1)) source.code = some (args, body) →
    findCode (some loc) (indices.map (fun n => holEl n env2)) target.code = some (args', body') →
    envRel false f args args' → noMutcons body →
    (body ≠ body' → ∃ workerLoc, optimisedCode loc workerLoc source.code target.code ∧
      rewriteWrapperSource loc workerLoc args.length body = some body') →
    evaluate [body] args (decClock (ticks + 1) source) = (bodyResult, bodyFinal) →
    bodyResult ≠ .err (.abort .typeError) →
    ListSimulation.Core [body'] args' f (decClock (ticks + 1) target) bodyResult bodyFinal

/-- Flapjack infrastructure: all four call-block simulation conclusions,
conditional on the smaller-clock ordinary and worker-body hypotheses. The
original measure and global induction hypothesis remain to be assembled. -/
theorem evaluate_cb_simulation {C F : Type} (loc : Nat) (cb : CallBlock)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [callBlockToBvi loc cb] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel opt f env1 env2)
    (states : stateRel f source target) (wf : wfBlock env1.length cb)
    (ordinaryIH : OrdinaryBodyIH loc source target env1 env2 f)
    (workerIH : ∀ dest, WorkerBodyIH loc dest source env1 env2 f) :
    ListSimulation.Core [callBlockToBvi loc cb] env2 f target result final ∧
    ∀ dest, optimisedCode loc dest source.code target.code →
      (∀ tag left child right, cb = .callBlock tag left child right →
        ListSimulation.Core [wrapperBlockSource tag left child right dest] env2 f target result final) ∧
      (∀ refs extras slot idx ptr, stateRefRel f source.refs refs →
        (∃ c, CallBlockEnvironment.allocHoleHasVal f refs extras slot idx c) →
        target.refs.domain ⊆ refs.domain → holEl slot extras = .refPtr false ptr →
        AuxCore cb dest env2 { target with refs := refs } f target.refs extras slot idx ptr result final) ∧
      (opt = true → ∀ ptr,
        (∃ c, holeHasVal f env1 env2 target.refs c) → holeNotFinalised target.refs ptr →
        holEl env1.length env2 = .refPtr false ptr →
        IfWorker.WorkerCore (workerBlockSource cb dest env1.length (env1.length + 1))
          env1 env2 f target ptr result final) := by
  refine ⟨CallBlockLeaf.evaluate_cb_ordinary loc cb source env1 opt f target env2 environments states ordinaryIH
    result final wf run notTypeError, ?_⟩
  intro dest code
  refine ⟨?_, ?_, ?_⟩
  · intro tag left child right shape
    subst cb
    exact evaluate_wrapper_cb loc dest tag left right child source target env1 env2 opt f result final
      environments states wf run notTypeError code (workerIH dest)
  · intro refs extras slot idx ptr heaps ⟨initial, hole⟩ domain pointer
    have modifiedStates : stateRel f source { target with refs := refs } := ⟨heaps, states.2⟩
    have modifiedCode : optimisedCode loc dest source.code ({ target with refs := refs } : BviState C F).code := code
    exact evaluate_aux_cb loc dest cb source env1 env2 opt f target.refs environments (workerIH dest)
      { target with refs := refs } extras slot idx ptr initial result final wf run notTypeError
      modifiedStates domain hole pointer modifiedCode
  · intro optTrue ptr ⟨initial, hole⟩ notFinal pointer
    subst opt
    exact CallBlockWorkerSimulation.evaluate_worker_cb loc dest ptr cb source target env1 env2 f initial result final
      run notTypeError environments wf states hole notFinal pointer code (workerIH dest)

end Flapjack.Compiler.Backend.BviTmc.CallBlockSimulation
