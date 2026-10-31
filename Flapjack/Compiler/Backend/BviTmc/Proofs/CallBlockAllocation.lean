import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockFrame
import Flapjack.Compiler.Backend.BviTmc.Proofs.FinaliseRelation

/-! Mutable constructor allocation for call-block wrappers. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallBlockAllocation
open BviTmc BviSem BvlSem

/-- Flapjack infrastructure: a mutable constructor frame allocates one fresh
unfinalised block with the selected variables in source order. -/
theorem evaluate_mutCons {C F : Type} (tag : Nat) (left right : List Nat)
    (env : List Value) (state : BviState C F)
    (leftWf : wfVars env.length left) (rightWf : wfVars env.length right) :
    evaluate [mutConsSource tag left right] env state =
      (.val [.refPtr false (leastUnusedRef state.refs)],
        { state with refs := state.refs.updateEq (leastUnusedRef state.refs,
          .mutBlock tag false (right.map (fun n => holEl n env)).reverse (.number 0)
            (left.map (fun n => holEl n env)).reverse) }) := by
  let leftVals := left.map (fun n => holEl n env)
  let rightVals := right.map (fun n => holEl n env)
  have leftRun := evaluate_vars_target left env.length env state leftWf (Nat.le_refl _)
  have rightRun := evaluate_vars_target right env.length env state rightWf (Nat.le_refl _)
  have zeroRun : evaluate [.op (.intOp (.const 0)) []] env state = (.val [.number 0], state) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate]
    simp [BviSem.evaluate, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
      BackendCommon.smallEnoughInt]
  have tailRun : evaluate ([.op (.intOp (.const 0)) []] ++ right.map Bvi.Exp.var) env state =
      (.val (.number 0 :: rightVals), state) := by
    change BviSem.evaluateTuple (_, env, state) = _
    rw [evaluateAppend]
    simp [BviSem.evaluateTuple, zeroRun, rightRun, rightVals]
  have argsRun : evaluate (left.map Bvi.Exp.var ++ [.op (.intOp (.const 0)) []] ++ right.map Bvi.Exp.var) env state =
      (.val (leftVals ++ .number 0 :: rightVals), state) := by
    simp only [List.append_assoc]
    change BviSem.evaluateTuple (_, env, state) = _
    rw [evaluateAppend]
    simp only [BviSem.evaluateTuple, leftRun]
    simp only [List.singleton_append] at tailRun
    simp [tailRun, leftVals]
  simp only [mutConsSource]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  have dropRight : (right.map (fun n => holEl n env)).reverse.drop (right.length + 1) = [] := by
    apply List.drop_eq_nil_of_le
    simp
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, leftVals, rightVals,
    List.reverse_append, List.drop_append, dropRight]

/-- Flapjack infrastructure: the freshly allocated constructor is a valid
auxiliary hole, and the pre-existing source heap remains related. -/
theorem alloc_frame_invariants {C F : Type} (tag : Nat) (left right : List Nat)
    (env : List Value) (source : BviState (Nat × C) F) (target : BviState C F)
    (f : HolFiniteMapExact Nat Nat) (states : stateRel f source target)
    (small : BackendCommon.smallEnoughInt (Int.ofNat right.length)) :
    let ptr := leastUnusedRef target.refs
    let refs := target.refs.updateEq (ptr,
      .mutBlock tag false (right.map (fun n => holEl n env)).reverse (.number 0)
        (left.map (fun n => holEl n env)).reverse)
    stateRefRel f source.refs refs ∧
      CallBlockEnvironment.allocHoleHasVal f refs [.refPtr false ptr] 0 right.length (.number 0) ∧
      target.refs.domain ⊆ refs.domain ∧ ptr ∉ target.refs.domain := by
  dsimp only
  have outside := fresh_not_in_range f source.refs target.refs states.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact stateRefRel_filled f source.refs target.refs _ _ states.1 (fun i h => outside ⟨i, h⟩)
  · refine ⟨leastUnusedRef target.refs, tag, (right.map (fun n => holEl n env)).reverse,
      (left.map (fun n => holEl n env)).reverse, by simp, rfl, ?_, ?_, outside, ?_⟩
    · simp
    · simpa using small
    · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  · intro key present
    exact BvlProps.refs_update_mono target.refs _ key _ present
  · simp [HolFiniteMapExact.domain, leastUnusedRef_unused]

/-- Flapjack infrastructure: a wrapper propagates errors from its auxiliary
worker after allocating the constructor frame. -/
theorem evaluate_wrapper_error {C F : Type} (tag : Nat) (left right : List Nat) (child : CallBlock)
    (dest : Nat) (env : List Value) (state next : BviState C F)
    (leftWf : wfVars env.length left) (rightWf : wfVars env.length right)
    (error : SemanticPrimitivesHOL.ErrorResult ExnOrRet)
    (workerRun : evaluate [workerAuxSource (shiftBlock 1 child) dest 0 right.length]
      (.refPtr false (leastUnusedRef state.refs) :: env)
      { state with refs := state.refs.updateEq (leastUnusedRef state.refs,
        .mutBlock tag false (right.map (fun n => holEl n env)).reverse (.number 0)
          (left.map (fun n => holEl n env)).reverse) } = (.err error, next)) :
    evaluate [wrapperBlockSource tag left child right dest] env state = (.err error, next) := by
  simp only [wrapperBlockSource]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, evaluate_mutCons tag left right env state leftWf rightWf]
  dsimp only
  simp only [List.singleton_append]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, workerRun]

/-- Flapjack infrastructure: a successful auxiliary worker is followed by
finalisation of the allocated constructor in the wrapper. -/
theorem evaluate_wrapper_success {C F : Type} (tag : Nat) (left right : List Nat) (child : CallBlock)
    (dest : Nat) (env : List Value) (state next : BviState C F)
    (leftWf : wfVars env.length left) (rightWf : wfVars env.length right)
    (value : Value) (refs : HolFiniteMapExact Nat (Ref Value))
    (workerRun : evaluate [workerAuxSource (shiftBlock 1 child) dest 0 right.length]
      (.refPtr false (leastUnusedRef state.refs) :: env)
      { state with refs := state.refs.updateEq (leastUnusedRef state.refs,
        .mutBlock tag false (right.map (fun n => holEl n env)).reverse (.number 0)
          (left.map (fun n => holEl n env)).reverse) } = (.val [unitValue], next))
    (finalise : finaliseCons (.refPtr false (leastUnusedRef state.refs)) next.refs = some (value, refs)) :
    evaluate [wrapperBlockSource tag left child right dest] env state =
      (.val [value], { next with refs := refs }) := by
  simp only [wrapperBlockSource]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, evaluate_mutCons tag left right env state leftWf rightWf]
  dsimp only
  simp only [List.singleton_append]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, workerRun]
  dsimp only
  rw [BviSem.evaluate, BviSem.fixClock_evaluate]
  simp [BviSem.evaluate, BviTailrec.doApp_finaliseCons_effect, BviTailrec.finaliseConsEffect, finalise]

end Flapjack.Compiler.Backend.BviTmc.CallBlockAllocation
