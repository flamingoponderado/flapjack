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

/-- Flapjack infrastructure: after the worker has used the newly allocated
frame as its only writable hole, its heap guarantees also hold for the heap
that existed before the wrapper allocated that frame. -/
theorem wrapper_frame_invariants (f g : HolFiniteMapExact Nat Nat)
    (refs nextRefs : HolFiniteMapExact Nat (Ref Value)) (tag : Nat) (left right : List Value)
    (child : Value)
    (fresh : onlyFresh f g (refs.updateEq (leastUnusedRef refs,
      .mutBlock tag false left child right)))
    (unchanged : holesUnchangedExcept f (refs.updateEq (leastUnusedRef refs,
      .mutBlock tag false left child right)) nextRefs {leastUnusedRef refs})
    (unfinalised : holesStillNotFinalised f (refs.updateEq (leastUnusedRef refs,
      .mutBlock tag false left child right)) nextRefs) :
    onlyFresh f g refs ∧ holesUnchangedExcept f refs nextRefs ∅ ∧
      holesStillNotFinalised f refs nextRefs := by
  classical
  have sameUpdate : @HolFiniteMapExact.updateEq Nat (Ref Value) (Classical.decEq Nat) refs
      (leastUnusedRef refs, .mutBlock tag false left child right) =
      @HolFiniteMapExact.updateEq Nat (Ref Value) instDecidableEqNat refs
        (leastUnusedRef refs, .mutBlock tag false left child right) := by
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨onlyFresh_delete_frame f g refs _ _ fresh, ?_, ?_⟩
  · have relation := holesUnchanged_delete_fresh f refs nextRefs (leastUnusedRef refs)
      (.mutBlock tag false left child right)
    apply relation ?_ (by
      simp [HolFiniteMapExact.domain, leastUnusedRef_unused])
    simpa only [sameUpdate] using unchanged
  · apply holesStill_delete f refs nextRefs (leastUnusedRef refs) tag left child right
    simpa only [sameUpdate] using unfinalised

/-- Flapjack infrastructure: the auxiliary worker leaves the allocated
wrapper frame's constructor tag and surrounding fields intact while filling
its hole. Its reported hole is the original frame and stays outside the new
pointer-map range. -/
theorem wrapper_frame_contents (f g : HolFiniteMapExact Nat Nat)
    (refs nextRefs : HolFiniteMapExact Nat (Ref Value)) (ptr tag : Nat)
    (left right : List Value) (initial child : Value)
    (outside : ptr ∉ mapRange f)
    (unchanged : holesUnchangedExcept f (refs.updateEq (ptr,
      .mutBlock tag false left initial right)) nextRefs {ptr})
    (hole : CallBlockEnvironment.allocHoleHasVal g nextRefs [.refPtr false ptr] 0 left.length child) :
    ptr ∉ mapRange g ∧ nextRefs.lookup ptr = some (.mutBlock tag false left child right) := by
  obtain ⟨holePtr, holeTag, holeLeft, holeRight, _, ptrEq, _, _, holeOutside, holeFound⟩ := hole
  have same : holePtr = ptr := by simpa [holEl, holHd] using ptrEq.symm
  subst holePtr
  have initialFound : (refs.updateEq (ptr, .mutBlock tag false left initial right)).lookup ptr =
      some (.mutBlock tag false left initial right) := by
    simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  obtain ⟨finalised, nextChild, preserved, _⟩ :=
    unchanged ptr tag false left initial right outside initialFound
  rw [holeFound] at preserved
  cases preserved
  exact ⟨holeOutside, holeFound⟩

/-- Flapjack infrastructure: a successfully filled wrapper frame and its
related child form a mutable constructor chain that can be finalised while
preserving the heap relations. This is the successful wrapper's finalisation
step, conditional on the auxiliary worker's simulation result. -/
theorem wrapper_finalise_frame (f g : HolFiniteMapExact Nat Nat)
    (oldRefs nextRefs sourceRefs : HolFiniteMapExact Nat (Ref Value)) (tag : Nat)
    (left right sourceLeft sourceRight : List Value) (initial child sourceChild : Value)
    (outside : leastUnusedRef oldRefs ∉ mapRange f)
    (unchanged : holesUnchangedExcept f (oldRefs.updateEq (leastUnusedRef oldRefs,
      .mutBlock tag false left initial right)) nextRefs {leastUnusedRef oldRefs})
    (hole : CallBlockEnvironment.allocHoleHasVal g nextRefs [.refPtr false (leastUnusedRef oldRefs)]
      0 left.length child)
    (inner : mutableBlockRel g oldRefs (nextRefs.eraseEq (leastUnusedRef oldRefs)) sourceChild child)
    (leftRelated : List.Forall₂ (valueRel g) sourceLeft left)
    (rightRelated : List.Forall₂ (valueRel g) sourceRight right)
    (heaps : stateRefRel g sourceRefs nextRefs)
    (still : holesStillNotFinalised f oldRefs nextRefs) :
    ∃ value refs, finaliseCons (.refPtr false (leastUnusedRef oldRefs)) nextRefs = some (value, refs) ∧
      valueRel g (.block tag (sourceLeft ++ [sourceChild] ++ sourceRight)) value ∧
      stateRefRel g sourceRefs refs ∧ holesUnchangedExcept g nextRefs refs ∅ ∧
      holesStillNotFinalised f oldRefs refs := by
  obtain ⟨outsideNext, found⟩ := wrapper_frame_contents f g oldRefs nextRefs
    (leastUnusedRef oldRefs) tag left right initial child outside unchanged hole
  have absent : leastUnusedRef oldRefs ∉ oldRefs.domain := by
    simp [HolFiniteMapExact.domain, leastUnusedRef_unused]
  have block := mutableBlockRel_cons g oldRefs nextRefs (leastUnusedRef oldRefs) tag
    sourceLeft left sourceChild child sourceRight right inner leftRelated rightRelated found outsideNext absent
  exact FinaliseRelation.evaluate_finalise_cons _ nextRefs f g sourceRefs _ oldRefs heaps block still

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

/-- Flapjack infrastructure: the successful auxiliary simulation yields an
actual wrapper evaluation and a source-related final value. This assembles
allocation, the worker's heap guarantees, and finalisation; the auxiliary
simulation itself remains a separate proof obligation. -/
theorem evaluate_wrapper_success_related {C F : Type}
    (tag : Nat) (left right : List Nat) (child : CallBlock) (dest : Nat)
    (env : List Value) (state next : BviState C F)
    (f g : HolFiniteMapExact Nat Nat) (sourceRefs : HolFiniteMapExact Nat (Ref Value))
    (sourceLeft sourceRight : List Value) (sourceChild childValue : Value)
    (leftWf : wfVars env.length left) (rightWf : wfVars env.length right)
    (workerRun : evaluate [workerAuxSource (shiftBlock 1 child) dest 0 right.length]
      (.refPtr false (leastUnusedRef state.refs) :: env)
      { state with refs := state.refs.updateEq (leastUnusedRef state.refs,
        .mutBlock tag false (right.map (fun n => holEl n env)).reverse (.number 0)
          (left.map (fun n => holEl n env)).reverse) } = (.val [unitValue], next))
    (outside : leastUnusedRef state.refs ∉ mapRange f)
    (unchanged : holesUnchangedExcept f (state.refs.updateEq (leastUnusedRef state.refs,
      .mutBlock tag false (right.map (fun n => holEl n env)).reverse (.number 0)
        (left.map (fun n => holEl n env)).reverse)) next.refs {leastUnusedRef state.refs})
    (hole : CallBlockEnvironment.allocHoleHasVal g next.refs
      [.refPtr false (leastUnusedRef state.refs)] 0 right.length childValue)
    (inner : mutableBlockRel g state.refs (next.refs.eraseEq (leastUnusedRef state.refs)) sourceChild childValue)
    (leftRelated : List.Forall₂ (valueRel g) sourceLeft (right.map (fun n => holEl n env)).reverse)
    (rightRelated : List.Forall₂ (valueRel g) sourceRight (left.map (fun n => holEl n env)).reverse)
    (heaps : stateRefRel g sourceRefs next.refs) (still : holesStillNotFinalised f state.refs next.refs) :
    ∃ value refs, evaluate [wrapperBlockSource tag left child right dest] env state =
        (.val [value], { next with refs := refs }) ∧
      valueRel g (.block tag (sourceLeft ++ [sourceChild] ++ sourceRight)) value ∧
      stateRefRel g sourceRefs refs ∧ holesUnchangedExcept g next.refs refs ∅ ∧
      holesStillNotFinalised f state.refs refs := by
  have hole' : CallBlockEnvironment.allocHoleHasVal g next.refs
      [.refPtr false (leastUnusedRef state.refs)] 0
      (right.map (fun n => holEl n env)).reverse.length childValue := by
    simpa using hole
  obtain ⟨value, refs, finalise, related, heaps', unchanged', still'⟩ :=
    wrapper_finalise_frame f g state.refs next.refs sourceRefs tag
      (right.map (fun n => holEl n env)).reverse (left.map (fun n => holEl n env)).reverse
      sourceLeft sourceRight (.number 0) childValue sourceChild outside unchanged hole' inner
      leftRelated rightRelated heaps still
  exact ⟨value, refs, evaluate_wrapper_success tag left right child dest env state next
    leftWf rightWf value refs workerRun finalise, related, heaps', unchanged', still'⟩

end Flapjack.Compiler.Backend.BviTmc.CallBlockAllocation
