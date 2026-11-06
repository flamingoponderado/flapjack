import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockAuxSimulation
import Flapjack.Compiler.Backend.BviTmc.Proofs.FillHole

/-! Constructor frames in the optimized call-block worker. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallBlockWorkerFrame
open BviTmc BviSem BvlSem

/-- Flapjack infrastructure: an unfinalised worker hole can be used as an
allocated auxiliary hole at the corresponding environment slot. -/
theorem worker_hole_as_alloc (f : HolFiniteMapExact Nat Nat) (env1 env2 : List Value)
    (refs : HolFiniteMapExact Nat (Ref Value)) (ptr : Nat) (child : Value)
    (hole : holeHasVal f env1 env2 refs child) (notFinal : holeNotFinalised refs ptr)
    (pointer : holEl env1.length env2 = .refPtr false ptr) :
    ∃ idx, CallBlockEnvironment.allocHoleHasVal f refs env2 env1.length idx child ∧
      holEl (env1.length + 1) env2 = .number (Int.ofNat idx) := by
  obtain ⟨length, holePtr, tag, fin, left, right, ptrEq, idxEq, small, outside, found⟩ := hole
  rw [pointer] at ptrEq
  have same : holePtr = ptr := by simpa using ptrEq.symm
  subst holePtr
  obtain ⟨tag', left', child', right', unfinalised⟩ := notFinal
  rw [found] at unfinalised
  simp only [Option.some.injEq, Ref.mutBlock.injEq] at unfinalised
  have notFin : fin = false := unfinalised.2.1
  subst fin
  exact ⟨left.length, ⟨ptr, tag, left, right, by omega, pointer, rfl, small, outside, found⟩, idxEq⟩

/-- Flapjack infrastructure: returning an allocated hole at the original
worker slot reconstructs the worker hole relation. -/
theorem alloc_hole_as_worker (f : HolFiniteMapExact Nat Nat) (env1 env2 : List Value)
    (refs : HolFiniteMapExact Nat (Ref Value)) (ptr idx : Nat) (child : Value)
    (length : env2.length = env1.length + 2)
    (pointer : holEl env1.length env2 = .refPtr false ptr)
    (index : holEl (env1.length + 1) env2 = .number (Int.ofNat idx))
    (hole : CallBlockEnvironment.allocHoleHasVal f refs env2 env1.length idx child) :
    holeHasVal f env1 env2 refs child := by
  obtain ⟨holePtr, tag, left, right, _, ptrEq, idxEq, small, outside, found⟩ := hole
  rw [pointer] at ptrEq
  have same : holePtr = ptr := by simpa using ptrEq.symm
  subst holePtr
  exact ⟨length, ptr, tag, false, left, right, pointer, by simpa [idxEq] using index, small, outside, found⟩

/-- Flapjack infrastructure: a worker constructor frame links a new block to
the existing hole, then evaluates the shifted auxiliary child in that heap. -/
theorem evaluate_worker_frame {C F : Type} (dest tag ptr : Nat) (left right : List Nat)
    (child : CallBlock) (env1 env2 : List Value) (state : BviState C F)
    (f : HolFiniteMapExact Nat Nat) (initial : Value)
    (leftWf : wfVars env2.length left) (rightWf : wfVars env2.length right)
    (hole : holeHasVal f env1 env2 state.refs initial) (notFinal : holeNotFinalised state.refs ptr)
    (pointer : holEl env1.length env2 = .refPtr false ptr) :
    ∃ oldTag oldLeft oldRight,
      state.refs.lookup ptr = some (.mutBlock oldTag false oldLeft initial oldRight) ∧
      let fresh := leastUnusedRef state.refs
      let linked := (state.refs.updateEq (ptr, .mutBlock oldTag false oldLeft (.refPtr false fresh) oldRight)).updateEq
        (fresh, .mutBlock tag false (right.map (fun n => holEl n env2)).reverse (.number 0)
          (left.map (fun n => holEl n env2)).reverse)
      evaluate [workerBlockSource (.callBlock tag left child right) dest env1.length (env1.length + 1)] env2 state =
        evaluate [workerAuxSource (shiftBlock 2 child) dest 1 right.length]
          (unitValue :: .refPtr false fresh :: env2) { state with refs := linked } := by
  have length := hole.1
  obtain ⟨holePtr, oldTag, fin, oldLeft, oldRight, ptrEq, idxEq, small, outside, found⟩ := hole.2
  rw [pointer] at ptrEq
  have same : holePtr = ptr := by simpa using ptrEq.symm
  subst holePtr
  obtain ⟨tag', left', child', right', unfinalised⟩ := notFinal
  rw [found] at unfinalised
  simp only [Option.some.injEq, Ref.mutBlock.injEq] at unfinalised
  have finFalse : fin = false := unfinalised.2.1
  subst fin
  have different : ptr ≠ leastUnusedRef state.refs := by
    intro eq
    subst ptr
    rw [leastUnusedRef_unused] at found
    contradiction
  let fresh := leastUnusedRef state.refs
  let newBlock : Ref Value := .mutBlock tag false (right.map (fun n => holEl n env2)).reverse (.number 0)
    (left.map (fun n => holEl n env2)).reverse
  let allocated := { state with refs := state.refs.updateEq (fresh, newBlock) }
  have allocatedFound : allocated.refs.lookup ptr = some (.mutBlock oldTag false oldLeft initial oldRight) := by
    simpa [allocated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, fresh, different] using found
  have ptrBound : env1.length < env2.length := by omega
  have idxBound : env1.length + 1 < env2.length := by omega
  have ptrOpt : env2[env1.length]? = some (.refPtr false ptr) := by
    apply List.getElem?_eq_some_iff.mpr
    exact ⟨ptrBound, by simpa [holEl_eq_getElem env1.length env2 ptrBound] using pointer⟩
  have idxOpt : env2[env1.length + 1]? = some (.number (Int.ofNat oldLeft.length)) := by
    apply List.getElem?_eq_some_iff.mpr
    exact ⟨idxBound, by simpa [holEl_eq_getElem (env1.length + 1) env2 idxBound] using idxEq⟩
  have updateRun := FillHole.evaluate_fillHole_update (.var 0) (env1.length + 1) (env1.length + 2)
    ptr oldTag oldLeft initial oldRight (.refPtr false fresh :: env2) allocated allocated (.refPtr false fresh)
    (by simp [BviSem.evaluate]) (by simpa using ptrOpt) (by simpa [Nat.add_assoc] using idxOpt) allocatedFound
  have diff : ptr ≠ fresh := different
  have mapComm : (state.refs.updateEq (fresh, newBlock)).updateEq
        (ptr, .mutBlock oldTag false oldLeft (.refPtr false fresh) oldRight) =
      (state.refs.updateEq (ptr, .mutBlock oldTag false oldLeft (.refPtr false fresh) oldRight)).updateEq
        (fresh, newBlock) := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    by_cases a : key = ptr <;> by_cases b : key = fresh <;>
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, a, b, diff, Ne.symm diff] at *
  refine ⟨oldTag, oldLeft, oldRight, found, ?_⟩
  simp only [workerBlockSource]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate,
    CallBlockAllocation.evaluate_mutCons tag left right env2 state leftWf rightWf]
  dsimp only
  simp only [List.singleton_append]
  dsimp only [allocated, fresh, newBlock, fillHoleSource] at updateRun
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, updateRun]
  dsimp only
  simp only [List.singleton_append]
  dsimp only [fresh, newBlock] at mapComm
  rw [mapComm]

private theorem reverse_related (f : HolFiniteMapExact Nat Nat) {xs ys : List Value}
    (related : List.Forall₂ (valueRel f) xs ys) : List.Forall₂ (valueRel f) xs.reverse ys.reverse := by
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
    have appendRelated : ∀ {a b c d : List Value}, List.Forall₂ (valueRel f) a b →
        List.Forall₂ (valueRel f) c d → List.Forall₂ (valueRel f) (a ++ c) (b ++ d) := by
      intro a b c d first second
      induction first with
      | nil => exact second
      | cons h t rest => exact .cons h rest
    simpa using appendRelated ih (.cons head .nil)

/-- Flapjack infrastructure: the optimized worker constructor case follows
from auxiliary simulation of its child and the smaller-clock body hypothesis.
The other call-block conclusions and the original measure are omitted. -/
theorem evaluate_worker_frame_core {C F : Type} (loc dest tag ptr : Nat) (left right : List Nat)
    (child : CallBlock) (source : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 : List Value) (f : HolFiniteMapExact Nat Nat) (initial : Value)
    (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [callBlockToBvi loc (.callBlock tag left child right)] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel true f env1 env2)
    (states : stateRel f source target) (wf : wfBlock env1.length (.callBlock tag left child right))
    (hole : holeHasVal f env1 env2 target.refs initial) (notFinal : holeNotFinalised target.refs ptr)
    (pointer : holEl env1.length env2 = .refPtr false ptr)
    (code : optimisedCode loc dest source.code target.code)
    (bodyIH : CallBlockAuxSimulation.WorkerBodyIH loc dest source env1 env2 f) :
    IfWorker.WorkerCore (workerBlockSource (.callBlock tag left child right) dest env1.length (env1.length + 1))
      env1 env2 f target ptr result final := by
  have targetLength := envRel_length true f env1 env2 environments
  have targetLeft := wfVars_expand env1.length env2.length left wf.1 targetLength
  have targetRight := wfVars_expand env1.length env2.length right wf.2.2.1 targetLength
  obtain ⟨idx, initialHole, index⟩ := worker_hole_as_alloc f env1 env2 target.refs ptr initial hole notFinal pointer
  have small : BackendCommon.smallEnoughInt (Int.ofNat (right.map (fun n => holEl n env2)).reverse.length) := by
    simpa using wf.2.2.2
  obtain ⟨oldTag, oldLeft, oldRight, oldFound, different, linkedHeaps, newHole, domain, _, _⟩ :=
    CallBlockAuxFrame.link_frame_invariants f source.refs target.refs env2 env1.length ptr idx tag
      (right.map (fun n => holEl n env2)).reverse (left.map (fun n => holEl n env2)).reverse
      initial states.1 initialHole pointer small
  obtain ⟨tag', left', right', found', frameRun⟩ :=
    evaluate_worker_frame dest tag ptr left right child env1 env2 target f initial targetLeft targetRight hole notFinal pointer
  rw [oldFound] at found'
  simp only [Option.some.injEq, Ref.mutBlock.injEq] at found'
  obtain ⟨rfl, _, rfl, _, rfl⟩ := found'
  let linked := (target.refs.updateEq (ptr,
    .mutBlock oldTag false oldLeft (.refPtr false (leastUnusedRef target.refs)) oldRight)).updateEq
      (leastUnusedRef target.refs, .mutBlock tag false (right.map (fun n => holEl n env2)).reverse (.number 0)
        (left.map (fun n => holEl n env2)).reverse)
  let nextTarget := { target with refs := linked }
  have childStates : stateRel f source nextTarget := ⟨linkedHeaps, states.2⟩
  have childCode : optimisedCode loc dest source.code nextTarget.code := code
  have newHole' : CallBlockEnvironment.allocHoleHasVal f linked
      [unitValue, .refPtr false (leastUnusedRef target.refs)] 1 right.length (.number 0) := by
    have fullHole : CallBlockEnvironment.allocHoleHasVal f linked
        (unitValue :: .refPtr false (leastUnusedRef target.refs) :: env2) 1 right.length (.number 0) := by
      simpa using newHole
    exact CallBlockWorkerLeaf.alloc_hole_reindex f linked
      (unitValue :: .refPtr false (leastUnusedRef target.refs) :: env2)
      [unitValue, .refPtr false (leastUnusedRef target.refs)] 1 1 right.length
      (leastUnusedRef target.refs) (.number 0) fullHole (by simp [holEl, holHd])
      (by simp) (by simp [holEl, holHd])
  rw [CallBlockFrame.evaluate_frame loc tag left right child env1 source wf.1 wf.2.2.1] at run
  cases childRun : evaluate [callBlockToBvi loc child] env1 source with
  | mk childResult mid =>
    have childSafe : childResult ≠ .err (.abort .typeError) := by
      intro bad
      subst childResult
      simp [childRun] at run
      exact notTypeError run.1.symm
    obtain ⟨targetResult, next, g, childTargetRun, related, nextStates, extension, fresh, unchanged, still, success⟩ :=
      CallBlockAuxSimulation.evaluate_aux_cb loc dest child source env1 env2 true f target.refs environments bodyIH
        nextTarget [unitValue, .refPtr false (leastUnusedRef target.refs)] 1 right.length (leastUnusedRef target.refs)
        (.number 0) childResult mid wf.2.1 childRun childSafe childStates domain newHole'
        (by simp [holEl, holHd]) childCode
    have targetRun : evaluate [workerBlockSource (.callBlock tag left child right) dest env1.length (env1.length + 1)]
        env2 target = (targetResult, next) := by
      rw [frameRun]
      simpa [CallBlockAuxFrame.AuxCore, nextTarget, linked] using childTargetRun
    have invariants := CallBlockAuxFrame.linked_frame_return_invariants f g target.refs next.refs ptr oldTag tag oldLeft oldRight
      (right.map (fun n => holEl n env2)).reverse (left.map (fun n => holEl n env2)).reverse
      initial oldFound fresh unchanged still
    have returnedHole := CallBlockAuxFrame.linked_frame_old_hole f target.refs next.refs env2 env1.length ptr idx
      oldTag tag oldLeft oldRight (right.map (fun n => holEl n env2)).reverse
      (left.map (fun n => holEl n env2)).reverse initial initialHole pointer oldFound unchanged still
    cases childResult with
    | err error =>
      simp [childRun] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      exact ⟨targetResult, g, next, targetRun, related, nextStates, extension,
        invariants.1, invariants.2.1, invariants.2.2, by intro _ impossible; cases impossible⟩
    | val values =>
      obtain ⟨sourceValue, rfl⟩ := evaluate_singleton _ env1 source mid values childRun
      obtain ⟨targetValue, childBlocks, childHole⟩ := success sourceValue rfl
      have newHoleNext := CallBlockAllocation.alloc_hole_advance f g linked next.refs
        [unitValue, .refPtr false (leastUnusedRef target.refs)] 1 right.length (.number 0) targetValue
        newHole' childHole fresh
      have singleHole := CallBlockWorkerLeaf.alloc_hole_reindex g next.refs
        [unitValue, .refPtr false (leastUnusedRef target.refs)] [.refPtr false (leastUnusedRef target.refs)]
        1 0 right.length (leastUnusedRef target.refs) targetValue newHoleNext
        (by simp [holEl, holHd]) (by simp) (by simp [holEl, holHd])
      have leftRelated := CallBlockEnvironment.wfVars_list_rel left true f env1 env2 environments wf.1
      have rightRelated := CallBlockEnvironment.wfVars_list_rel right true f env1 env2 environments wf.2.2.1
      have leftNext := listRel_submap f g _ _ leftRelated extension
      have rightNext := listRel_submap f g _ _ rightRelated extension
      have freshOutside := fresh_not_in_range f source.refs target.refs states.1
      have blocks := CallBlockAuxFrame.linked_frame_block_relation f g target.refs target.refs next.refs ptr oldTag tag oldLeft oldRight
        (right.map (fun n => holEl n env2)).reverse (left.map (fun n => holEl n env2)).reverse
        (right.map (fun n => holEl n env1)).reverse (left.map (fun n => holEl n env1)).reverse
        sourceValue targetValue returnedHole.2 different (Set.Subset.rfl) freshOutside unchanged
        (by simpa using singleHole) childBlocks (reverse_related g rightNext) (reverse_related g leftNext)
      have workerHole := alloc_hole_as_worker f env1 env2 next.refs ptr idx (.refPtr false (leastUnusedRef target.refs))
        hole.1 pointer index returnedHole.1
      simp [childRun, holHd] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      refine ⟨targetResult, g, next, targetRun, ?_, nextStates, extension,
        invariants.1, invariants.2.1, invariants.2.2, ?_⟩
      · cases targetResult with
        | err error => simp [ResultRelation.optResRel] at related
        | val values =>
          cases values with
          | nil => simp [ResultRelation.optResRel] at related
          | cons value rest =>
            cases rest with
            | cons _ _ => simp [ResultRelation.optResRel] at related
            | nil =>
              cases value with
              | block blockTag fields => cases blockTag <;> cases fields <;> simp_all [ResultRelation.optResRel]
              | number _ | word64 _ | codePtr _ | refPtr _ _ => simp_all [ResultRelation.optResRel]
      · intro sourceBlock equal
        cases equal
        exact ⟨.refPtr false (leastUnusedRef target.refs), by simpa using blocks, workerHole⟩

end Flapjack.Compiler.Backend.BviTmc.CallBlockWorkerFrame
