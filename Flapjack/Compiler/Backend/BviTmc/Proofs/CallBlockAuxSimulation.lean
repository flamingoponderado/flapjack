import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockAuxFrame

/-! Auxiliary simulation of complete call blocks. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallBlockAuxSimulation
open BviTmc BviSem BvlSem CallBlockAuxFrame

/-- Flapjack infrastructure: the smaller-clock function-body worker
induction hypothesis used by recursive call-block leaves. -/
def WorkerBodyIH {C F : Type} (loc dest : Nat) (source : BviState (Nat × C) F)
    (env1 env2 : List Value) (f : HolFiniteMapExact Nat Nat) : Prop :=
  ∀ (ticks : Nat) (indices : List Nat) (target : BviState C F) (ptr idx : Nat) (initial : Value)
    (body worker : Bvi.Exp) (bodyResult : BviResult) (bodyFinal : BviState (Nat × C) F),
    wfVars env1.length indices → stateRel f source target → optimisedCode loc dest source.code target.code →
    findCode (some loc) (indices.map (fun n => holEl n env1)) source.code =
      some (indices.map (fun n => holEl n env1), body) →
    evaluate [body] (indices.map (fun n => holEl n env1)) (decClock (ticks + 1) source) =
      (bodyResult, bodyFinal) → bodyResult ≠ .err (.abort .typeError) → noMutcons body →
    rewriteWorkerSource loc dest indices.length (indices.length + 1) indices.length body = worker →
    envRel true f (indices.map (fun n => holEl n env1))
      (indices.map (fun n => holEl n env2) ++ [.refPtr false ptr, .number (Int.ofNat idx)]) →
    holeHasVal f (indices.map (fun n => holEl n env1))
      (indices.map (fun n => holEl n env2) ++ [.refPtr false ptr, .number (Int.ofNat idx)]) target.refs initial →
    holeNotFinalised target.refs ptr →
    IfWorker.WorkerCore worker (indices.map (fun n => holEl n env1))
      (indices.map (fun n => holEl n env2) ++ [.refPtr false ptr, .number (Int.ofNat idx)])
      f (decClock (ticks + 1) target) ptr bodyResult bodyFinal

/-- Flapjack infrastructure: auxiliary simulation of any well-formed call
block, assuming the original smaller-clock function-body worker induction.
The full theorem's other conclusions and measure are not included. -/
theorem evaluate_aux_cb {C F : Type} (loc dest : Nat) (cb : CallBlock)
    (source : BviState (Nat × C) F) (env1 env2 : List Value) (opt : Bool)
    (f : HolFiniteMapExact Nat Nat) (oldRefs : HolFiniteMapExact Nat (Ref Value))
    (environments : envRel opt f env1 env2) (bodyIH : WorkerBodyIH loc dest source env1 env2 f)
    (target : BviState C F) (extras : List Value) (slot idx ptr : Nat) (initial : Value)
    (result : BviResult) (final : BviState (Nat × C) F)
    (wf : wfBlock env1.length cb)
    (run : evaluate [callBlockToBvi loc cb] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (states : stateRel f source target)
    (domain : oldRefs.domain ⊆ target.refs.domain)
    (hole : CallBlockEnvironment.allocHoleHasVal f target.refs extras slot idx initial)
    (pointer : holEl slot extras = .refPtr false ptr) (code : optimisedCode loc dest source.code target.code) :
    AuxCore cb dest env2 target f oldRefs extras slot idx ptr result final := by
  induction cb generalizing target extras slot idx ptr initial result final with
  | rCall ticks indices =>
    apply CallBlockWorkerLeaf.evaluate_aux_rcall loc dest ticks indices source target env1 env2 extras opt f
      slot ptr idx oldRefs initial result final run notTypeError environments wf states hole pointer domain code
    intro body worker bodyResult found bodyRun safe noMut rewrite envRelated filled notFinal
    exact bodyIH ticks indices target ptr idx initial body worker bodyResult final wf states code found bodyRun safe
      noMut rewrite envRelated filled notFinal
  | callBlock tag left child right ih =>
    apply evaluate_aux_frame_core loc dest tag left right child source target env1 env2 extras opt f oldRefs
      slot idx ptr initial result final run notTypeError environments states wf domain hole pointer
    intro childResult mid linked childRun childSafe childStates childDomain childHole
    have childCode : optimisedCode loc dest source.code ({ target with refs := linked } : BviState C F).code := code
    apply ih { target with refs := linked } (unitValue :: .refPtr false (leastUnusedRef target.refs) :: extras)
      1 right.length (leastUnusedRef target.refs) (.number 0) childResult mid wf.2.1 childRun childSafe
      childStates childDomain childHole
    · simp [holEl, holHd]
    · exact childCode

/-- Flapjack infrastructure: simulation of the optimized wrapper for any
well-formed constructor call block, using the smaller-clock worker-body
induction hypothesis. -/
theorem evaluate_wrapper_cb {C F : Type} (loc dest tag : Nat) (left right : List Nat) (child : CallBlock)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (wf : wfBlock env1.length (.callBlock tag left child right))
    (run : evaluate [callBlockToBvi loc (.callBlock tag left child right)] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (code : optimisedCode loc dest source.code target.code)
    (bodyIH : WorkerBodyIH loc dest source env1 env2 f) :
    ListSimulation.Core [wrapperBlockSource tag left child right dest] env2 f target result final := by
  apply CallBlockAllocation.evaluate_wrapper_core loc dest tag left right child source target env1 env2 opt f
    result final run notTypeError environments states wf.1 wf.2.2.1 wf.2.2.2
  intro childResult mid childRun childSafe
  have alloc := CallBlockAllocation.alloc_frame_invariants tag left right env2 source target f states wf.2.2.2
  let refs := target.refs.updateEq (leastUnusedRef target.refs,
    .mutBlock tag false (right.map (fun n => holEl n env2)).reverse (.number 0)
      (left.map (fun n => holEl n env2)).reverse)
  let next := { target with refs := refs }
  have nextStates : stateRel f source next := ⟨alloc.1, states.2⟩
  have nextCode : optimisedCode loc dest source.code next.code := code
  have aux := evaluate_aux_cb loc dest child source env1 env2 opt f target.refs environments bodyIH next
    [.refPtr false (leastUnusedRef target.refs)] 0 right.length (leastUnusedRef target.refs) (.number 0)
    childResult mid wf.2.1 childRun childSafe nextStates alloc.2.2.1 alloc.2.1 (by simp [holEl, holHd]) nextCode
  simpa [AuxCore, next, refs] using aux

end Flapjack.Compiler.Backend.BviTmc.CallBlockAuxSimulation
