import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockAllocation
import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockWorkerLeaf

/-! Nested mutable frames in auxiliary call-block simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallBlockAuxFrame
open BviTmc BviSem BvlSem

/-- Flapjack infrastructure: the auxiliary portion of call-block simulation,
including its selected hole and the recursive mutable-block result. -/
def AuxCore {C F : Type} (cb : CallBlock) (dest : Nat) (env : List Value)
    (state : BviState C F) (f : HolFiniteMapExact Nat Nat)
    (oldRefs : HolFiniteMapExact Nat (Ref Value)) (extras : List Value) (slot idx ptr : Nat)
    (sourceResult : BviResult) (sourceFinal : BviState (Nat × C) F) : Prop :=
  ∃ result next g,
    evaluate [workerAuxSource (shiftBlock extras.length cb) dest slot idx] (extras ++ env) state = (result, next) ∧
    ResultRelation.optResRel g sourceResult result ∧ stateRel g sourceFinal next ∧ finiteSubmap f g ∧
    onlyFresh f g state.refs ∧ holesUnchangedExcept f state.refs next.refs {ptr} ∧
    holesStillNotFinalised f state.refs next.refs ∧
    ∀ sourceValue, sourceResult = .val [sourceValue] →
      ∃ targetValue, mutableBlockRel g oldRefs (next.refs.eraseEq ptr) sourceValue targetValue ∧
        CallBlockEnvironment.allocHoleHasVal f next.refs extras slot idx targetValue

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

/-- Flapjack infrastructure: linking a freshly allocated frame into the
current auxiliary hole preserves the source heap relation and provides the
unfinalised hole and heap-domain extension required by the recursive child. -/
theorem link_frame_invariants (f : HolFiniteMapExact Nat Nat)
    (sourceRefs refs : HolFiniteMapExact Nat (Ref Value)) (extras : List Value)
    (slot ptr idx tag : Nat) (newLeft newRight : List Value) (initial : Value)
    (heaps : stateRefRel f sourceRefs refs)
    (hole : CallBlockEnvironment.allocHoleHasVal f refs extras slot idx initial)
    (pointer : holEl slot extras = .refPtr false ptr)
    (small : BackendCommon.smallEnoughInt (Int.ofNat newLeft.length)) :
    let newPtr := leastUnusedRef refs
    ∃ oldTag oldLeft oldRight,
      let linked := (refs.updateEq (ptr, .mutBlock oldTag false oldLeft (.refPtr false newPtr) oldRight)).updateEq
        (newPtr, .mutBlock tag false newLeft (.number 0) newRight)
      refs.lookup ptr = some (.mutBlock oldTag false oldLeft initial oldRight) ∧
      ptr ≠ newPtr ∧ stateRefRel f sourceRefs linked ∧
      CallBlockEnvironment.allocHoleHasVal f linked (unitValue :: .refPtr false newPtr :: extras)
        1 newLeft.length (.number 0) ∧ refs.domain ⊆ linked.domain ∧
      linked.lookup ptr = some (.mutBlock oldTag false oldLeft (.refPtr false newPtr) oldRight) ∧
      linked.lookup newPtr = some (.mutBlock tag false newLeft (.number 0) newRight) := by
  dsimp only
  obtain ⟨holePtr, oldTag, oldLeft, oldRight, _, holePointer, _, _, outside, found⟩ := hole
  rw [pointer] at holePointer
  have same : holePtr = ptr := by simpa using holePointer.symm
  subst holePtr
  have freshOutside : leastUnusedRef refs ∉ mapRange f := fresh_not_in_range f sourceRefs refs heaps
  have different : ptr ≠ leastUnusedRef refs := by
    intro eq
    subst ptr
    rw [leastUnusedRef_unused] at found
    contradiction
  let first := refs.updateEq (ptr, .mutBlock oldTag false oldLeft (.refPtr false (leastUnusedRef refs)) oldRight)
  have firstHeaps : stateRefRel f sourceRefs first :=
    stateRefRel_filled f sourceRefs refs ptr _ heaps (fun i mapped => outside ⟨i, mapped⟩)
  have linkedHeaps := stateRefRel_filled f sourceRefs first (leastUnusedRef refs)
    (.mutBlock tag false newLeft (.number 0) newRight) firstHeaps
    (fun i mapped => freshOutside ⟨i, mapped⟩)
  refine ⟨oldTag, oldLeft, oldRight, found, different, linkedHeaps, ?_, ?_, ?_, ?_⟩
  · refine ⟨leastUnusedRef refs, tag, newLeft, newRight, by simp, ?_, rfl, small, freshOutside, ?_⟩
    · simp [holEl, holHd]
    · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  · intro key present
    exact BvlProps.refs_update_mono first _ key _ (BvlProps.refs_update_mono refs _ key _ present)
  · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different]
  · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- Flapjack infrastructure: after the recursive worker has changed only
the newly allocated hole, its freshness and hole-preservation guarantees
also hold for the original heap, allowing the old hole to have changed. -/
theorem linked_frame_return_invariants (f g : HolFiniteMapExact Nat Nat)
    (refs nextRefs : HolFiniteMapExact Nat (Ref Value)) (ptr oldTag newTag : Nat)
    (oldLeft oldRight newLeft newRight : List Value) (initial : Value)
    (found : refs.lookup ptr = some (.mutBlock oldTag false oldLeft initial oldRight))
    (fresh : onlyFresh f g ((refs.updateEq (ptr,
      .mutBlock oldTag false oldLeft (.refPtr false (leastUnusedRef refs)) oldRight)).updateEq
        (leastUnusedRef refs, .mutBlock newTag false newLeft (.number 0) newRight)))
    (unchanged : holesUnchangedExcept f ((refs.updateEq (ptr,
      .mutBlock oldTag false oldLeft (.refPtr false (leastUnusedRef refs)) oldRight)).updateEq
        (leastUnusedRef refs, .mutBlock newTag false newLeft (.number 0) newRight)) nextRefs {leastUnusedRef refs})
    (still : holesStillNotFinalised f ((refs.updateEq (ptr,
      .mutBlock oldTag false oldLeft (.refPtr false (leastUnusedRef refs)) oldRight)).updateEq
        (leastUnusedRef refs, .mutBlock newTag false newLeft (.number 0) newRight)) nextRefs) :
    onlyFresh f g refs ∧ holesUnchangedExcept f refs nextRefs {ptr} ∧
      holesStillNotFinalised f refs nextRefs := by
  classical
  have sameDec : Classical.decEq Nat = instDecidableEqNat := by
    funext a b
    exact Subsingleton.elim _ _
  have different : ptr ≠ leastUnusedRef refs := by
    intro eq
    subst ptr
    rw [leastUnusedRef_unused] at found
    contradiction
  let first := refs.updateEq (ptr, .mutBlock oldTag false oldLeft (.refPtr false (leastUnusedRef refs)) oldRight)
  have newFresh : leastUnusedRef refs ∉ first.domain := by
    simp [first, HolFiniteMapExact.domain, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
      Ne.symm different, leastUnusedRef_unused]
  have reducedUnchanged : holesUnchangedExcept f first nextRefs ∅ := by
    have h := holesUnchanged_delete_fresh f first nextRefs (leastUnusedRef refs)
      (.mutBlock newTag false newLeft (.number 0) newRight)
    rw [sameDec] at h
    exact h unchanged newFresh
  have reducedStill : holesStillNotFinalised f first nextRefs := by
    have h := holesStill_delete f first nextRefs (leastUnusedRef refs) newTag newLeft (.number 0) newRight
    rw [sameDec] at h
    exact h still
  have oldUnchanged : holesUnchangedExcept f refs nextRefs {ptr} := by
    have h := holesUnchanged_changed f refs nextRefs () ptr oldTag false oldLeft
      (.refPtr false (leastUnusedRef refs)) oldRight false initial
    rw [sameDec] at h
    exact h reducedUnchanged found
  have oldStill : holesStillNotFinalised f refs nextRefs := by
    have h := holesStill_delete f refs nextRefs ptr oldTag oldLeft (.refPtr false (leastUnusedRef refs)) oldRight
    rw [sameDec] at h
    exact h reducedStill
  exact ⟨onlyFresh_delete_frame f g refs ptr _ (onlyFresh_delete_frame f g first _ _ fresh), oldUnchanged, oldStill⟩

/-- Flapjack infrastructure: recursion through the newly linked frame keeps
the original auxiliary hole unfinalised and containing the new frame pointer. -/
theorem linked_frame_old_hole (f : HolFiniteMapExact Nat Nat)
    (refs nextRefs : HolFiniteMapExact Nat (Ref Value)) (extras : List Value)
    (slot ptr idx oldTag newTag : Nat) (oldLeft oldRight newLeft newRight : List Value) (initial : Value)
    (hole : CallBlockEnvironment.allocHoleHasVal f refs extras slot idx initial)
    (pointer : holEl slot extras = .refPtr false ptr)
    (oldFound : refs.lookup ptr = some (.mutBlock oldTag false oldLeft initial oldRight))
    (unchanged :
      holesUnchangedExcept f ((refs.updateEq (ptr,
        .mutBlock oldTag false oldLeft (.refPtr false (leastUnusedRef refs)) oldRight)).updateEq
          (leastUnusedRef refs, .mutBlock newTag false newLeft (.number 0) newRight)) nextRefs {leastUnusedRef refs})
    (still :
      holesStillNotFinalised f ((refs.updateEq (ptr,
        .mutBlock oldTag false oldLeft (.refPtr false (leastUnusedRef refs)) oldRight)).updateEq
          (leastUnusedRef refs, .mutBlock newTag false newLeft (.number 0) newRight)) nextRefs) :
    CallBlockEnvironment.allocHoleHasVal f nextRefs extras slot idx (.refPtr false (leastUnusedRef refs)) ∧
      nextRefs.lookup ptr = some (.mutBlock oldTag false oldLeft (.refPtr false (leastUnusedRef refs)) oldRight) := by
  obtain ⟨holePtr, tag, left, right, bound, holePointer, index, small, outside, found⟩ := hole
  rw [pointer] at holePointer
  have same : holePtr = ptr := by simpa using holePointer.symm
  subst holePtr
  rw [oldFound] at found
  simp only [Option.some.injEq, Ref.mutBlock.injEq] at found
  obtain ⟨rfl, _, rfl, _, rfl⟩ := found
  have found := oldFound
  have different : ptr ≠ leastUnusedRef refs := by
    intro eq
    subst ptr
    rw [leastUnusedRef_unused] at found
    contradiction
  have linkedFound : ((refs.updateEq (ptr,
      .mutBlock oldTag false oldLeft (.refPtr false (leastUnusedRef refs)) oldRight)).updateEq
        (leastUnusedRef refs, .mutBlock newTag false newLeft (.number 0) newRight)).lookup ptr =
      some (.mutBlock oldTag false oldLeft (.refPtr false (leastUnusedRef refs)) oldRight) := by
    simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different]
  obtain ⟨fin, newChild, preserved, unchangedChild⟩ :=
    unchanged ptr oldTag false oldLeft (.refPtr false (leastUnusedRef refs)) oldRight outside linkedFound
  have sameChild := unchangedChild (by simpa using different)
  subst newChild
  have initialNotFinal : holeNotFinalised ((refs.updateEq (ptr,
      .mutBlock oldTag false oldLeft (.refPtr false (leastUnusedRef refs)) oldRight)).updateEq
        (leastUnusedRef refs, .mutBlock newTag false newLeft (.number 0) newRight)) ptr :=
    ⟨oldTag, oldLeft, .refPtr false (leastUnusedRef refs), oldRight, linkedFound⟩
  obtain ⟨tag', left', child', right', finalFound⟩ := still ptr outside initialNotFinal
  rw [preserved] at finalFound
  simp only [Option.some.injEq, Ref.mutBlock.injEq] at finalFound
  have notFinal : fin = false := finalFound.2.1
  subst fin
  exact ⟨⟨ptr, oldTag, oldLeft, oldRight, bound, pointer, index, small, outside, preserved⟩, preserved⟩

/-- Flapjack infrastructure: after recursion, the newly linked frame extends
the child's mutable-block relation to the enclosing source constructor. The
old parent hole is removed from the recursive heap before taking that step. -/
theorem linked_frame_block_relation (f g : HolFiniteMapExact Nat Nat)
    (oldRefs refs nextRefs : HolFiniteMapExact Nat (Ref Value)) (ptr oldTag newTag : Nat)
    (oldLeft oldRight newLeft newRight sourceLeft sourceRight : List Value)
    (sourceChild targetChild : Value)
    (oldLookup : nextRefs.lookup ptr = some (.mutBlock oldTag false oldLeft
      (.refPtr false (leastUnusedRef refs)) oldRight))
    (different : ptr ≠ leastUnusedRef refs) (oldDomain : oldRefs.domain ⊆ refs.domain)
    (freshOutside : leastUnusedRef refs ∉ mapRange f)
    (unchanged : holesUnchangedExcept f ((refs.updateEq (ptr,
      .mutBlock oldTag false oldLeft (.refPtr false (leastUnusedRef refs)) oldRight)).updateEq
        (leastUnusedRef refs, .mutBlock newTag false newLeft (.number 0) newRight)) nextRefs {leastUnusedRef refs})
    (childHole : CallBlockEnvironment.allocHoleHasVal g nextRefs
      [.refPtr false (leastUnusedRef refs)] 0 newLeft.length targetChild)
    (childBlocks : mutableBlockRel g oldRefs (nextRefs.eraseEq (leastUnusedRef refs)) sourceChild targetChild)
    (leftRelated : List.Forall₂ (valueRel g) sourceLeft newLeft)
    (rightRelated : List.Forall₂ (valueRel g) sourceRight newRight) :
    mutableBlockRel g oldRefs (nextRefs.eraseEq ptr)
      (.block newTag (sourceLeft ++ [sourceChild] ++ sourceRight)) (.refPtr false (leastUnusedRef refs)) := by
  let fresh := leastUnusedRef refs
  let first := refs.updateEq (ptr, .mutBlock oldTag false oldLeft (.refPtr false fresh) oldRight)
  have different' : ptr ≠ fresh := different
  obtain ⟨outsideNext, childLookup⟩ := CallBlockAllocation.wrapper_frame_contents f g first nextRefs fresh
    newTag newLeft newRight (.number 0) targetChild freshOutside unchanged childHole
  have oldLookupErased : (nextRefs.eraseEq fresh).lookup ptr =
      some (.mutBlock oldTag false oldLeft (.refPtr false fresh) oldRight) := by
    simpa [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, different'] using oldLookup
  have freshMissing : fresh ∉ (nextRefs.eraseEq fresh).domain := by
    simp [HolFiniteMapExact.domain, HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL]
  have freshOld : fresh ∉ oldRefs.domain := by
    intro present
    have inRefs := oldDomain present
    have missing : fresh ∉ refs.domain := by simp [fresh, HolFiniteMapExact.domain, leastUnusedRef_unused]
    exact missing inRefs
  have reduced := mutableBlockRel_delete g oldRefs (nextRefs.eraseEq fresh) sourceChild targetChild ptr oldTag
    oldLeft fresh oldRight childBlocks oldLookupErased freshMissing freshOld outsideNext
  have eraseComm : (nextRefs.eraseEq fresh).eraseEq ptr = (nextRefs.eraseEq ptr).eraseEq fresh := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    by_cases a : key = ptr <;> by_cases b : key = fresh <;>
      simp [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, a, b]
  have inner : mutableBlockRel g oldRefs ((nextRefs.eraseEq ptr).eraseEq fresh) sourceChild targetChild := by
    simpa only [eraseComm] using reduced
  have childLookupErased : (nextRefs.eraseEq ptr).lookup fresh =
      some (.mutBlock newTag false newLeft targetChild newRight) := by
    simpa [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, Ne.symm different'] using childLookup
  exact mutableBlockRel_cons g oldRefs (nextRefs.eraseEq ptr) fresh newTag sourceLeft newLeft
    sourceChild targetChild sourceRight newRight inner leftRelated rightRelated childLookupErased outsideNext freshOld

/-- Flapjack infrastructure: the auxiliary frame's constant-index update
stores the new frame pointer into an unfinalised old hole and returns unit. -/
theorem evaluate_update_const {C F : Type} (ptrIndex idx ptr tag : Nat)
    (left right : List Value) (oldChild newChild : Value) (env : List Value) (state : BviState C F)
    (ptrAt : env[ptrIndex]? = some (.refPtr false ptr)) (valueAt : env[0]? = some newChild)
    (index : idx = left.length) (small : BackendCommon.smallEnoughInt (Int.ofNat idx))
    (found : state.refs.lookup ptr = some (.mutBlock tag false left oldChild right)) :
    evaluate [updateConsSource (.var ptrIndex) (.op (.intOp (.const (Int.ofNat idx))) []) (.var 0)] env state =
      (.val [unitValue], { state with refs := state.refs.updateEq (ptr, .mutBlock tag false left newChild right) }) := by
  have valueRun : evaluate [.var 0] env state = (.val [newChild], state) := by
    simp [BviSem.evaluate, valueAt]
  have ptrRun : evaluate [.var ptrIndex] env state = (.val [.refPtr false ptr], state) := by
    simp [BviSem.evaluate, ptrAt]
  have idxRun : evaluate [.op (.intOp (.const (Int.ofNat idx))) []] env state =
      (.val [.number (Int.ofNat idx)], state) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate]
    simp only [BviSem.evaluate, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux]
    simp only [BackendCommon.smallEnoughInt] at small ⊢
    split <;> simp_all
  have tailRun : evaluate [.op (.intOp (.const (Int.ofNat idx))) [], .var ptrIndex] env state =
      (.val [.number (Int.ofNat idx), .refPtr false ptr], state) := by
    change evaluateTuple ([_] ++ [_], env, state) = _
    rw [evaluateAppend]
    simp only [BviSem.evaluateTuple]
    rw [idxRun]
    dsimp only
    rw [ptrRun]
    rfl
  have operands : evaluate [.var 0, .op (.intOp (.const (Int.ofNat idx))) [], .var ptrIndex] env state =
      (.val [newChild, .number (Int.ofNat idx), .refPtr false ptr], state) := by
    change evaluateTuple ([_] ++ [_, _], env, state) = _
    rw [evaluateAppend]
    simp only [BviSem.evaluateTuple]
    rw [valueRun]
    dsimp only
    rw [tailRun]
    rfl
  simp only [updateConsSource]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, operands]
  simp [BviTailrec.doApp_updateCons_effect, BviTailrec.updateConsEffect, found, index]

/-- Flapjack infrastructure: allocating a constructor with shifted indices
under a prefixed environment reads the same frame fields as the unshifted
constructor. -/
theorem evaluate_shifted_mutCons {C F : Type} (tag : Nat) (left right : List Nat)
    (extras env : List Value) (state : BviState C F)
    (leftWf : wfVars env.length left) (rightWf : wfVars env.length right) :
    evaluate [mutConsSource tag (shiftVars extras.length left) (shiftVars extras.length right)]
        (extras ++ env) state =
      (.val [.refPtr false (leastUnusedRef state.refs)],
        { state with refs := state.refs.updateEq (leastUnusedRef state.refs,
          .mutBlock tag false (right.map (fun n => holEl n env)).reverse (.number 0)
            (left.map (fun n => holEl n env)).reverse) }) := by
  have shiftedWf (vars : List Nat) (wf : wfVars env.length vars) :
      wfVars (extras ++ env).length (shiftVars extras.length vars) := by
    simpa [List.length_append] using wfVars_shift env.length extras.length vars wf
  have valuesEq (vars : List Nat) (wf : wfVars env.length vars) :
      (shiftVars extras.length vars).map (fun n => holEl n (extras ++ env)) =
        vars.map (fun n => holEl n env) := by
    have shifted := evaluate_vars_target (shiftVars extras.length vars) (extras ++ env).length
      (extras ++ env) state (shiftedWf vars wf) (Nat.le_refl _)
    have original := evaluate_vars_target vars env.length env state wf (Nat.le_refl _)
    have equal := evaluate_shift_vars vars env state extras
    rw [shifted, original] at equal
    have results := congrArg Prod.fst equal
    exact SemanticPrimitivesHOL.Result.val.inj results
  have run := CallBlockAllocation.evaluate_mutCons tag (shiftVars extras.length left)
    (shiftVars extras.length right) (extras ++ env) state (shiftedWf left leftWf) (shiftedWf right rightWf)
  simpa [valuesEq left leftWf, valuesEq right rightWf] using run

/-- Flapjack infrastructure: an auxiliary constructor frame allocates its
new block, links it into the current hole, and continues with the shifted
child and the two new environment entries. -/
theorem evaluate_aux_frame {C F : Type} (tag dest slot idx ptr : Nat)
    (left right : List Nat) (child : CallBlock) (extras env : List Value) (state : BviState C F)
    (f : HolFiniteMapExact Nat Nat) (initial : Value)
    (leftWf : wfVars env.length left) (rightWf : wfVars env.length right)
    (hole : CallBlockEnvironment.allocHoleHasVal f state.refs extras slot idx initial)
    (pointer : holEl slot extras = .refPtr false ptr) :
    ∃ oldTag oldLeft oldRight,
      state.refs.lookup ptr = some (.mutBlock oldTag false oldLeft initial oldRight) ∧
      let fresh := leastUnusedRef state.refs
      let linked := (state.refs.updateEq (ptr, .mutBlock oldTag false oldLeft (.refPtr false fresh) oldRight)).updateEq
        (fresh, .mutBlock tag false (right.map (fun n => holEl n env)).reverse (.number 0)
          (left.map (fun n => holEl n env)).reverse)
      evaluate [workerAuxSource (shiftBlock extras.length (.callBlock tag left child right)) dest slot idx]
          (extras ++ env) state =
        evaluate [workerAuxSource (shiftBlock (extras.length + 2) child) dest 1 right.length]
          (unitValue :: .refPtr false fresh :: extras ++ env) { state with refs := linked } := by
  obtain ⟨holePtr, oldTag, oldLeft, oldRight, bound, holePointer, index, small, outside, found⟩ := hole
  rw [pointer] at holePointer
  have same : holePtr = ptr := by simpa using holePointer.symm
  subst holePtr
  have different : ptr ≠ leastUnusedRef state.refs := by
    intro eq
    subst ptr
    rw [leastUnusedRef_unused] at found
    contradiction
  let fresh := leastUnusedRef state.refs
  let newBlock : Ref Value := .mutBlock tag false (right.map (fun n => holEl n env)).reverse (.number 0)
    (left.map (fun n => holEl n env)).reverse
  let allocated := { state with refs := state.refs.updateEq (fresh, newBlock) }
  have allocatedFound : allocated.refs.lookup ptr = some (.mutBlock oldTag false oldLeft initial oldRight) := by
    simpa [allocated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, fresh, different] using found
  have ptrAt : (.refPtr false fresh :: extras ++ env)[slot + 1]? = some (.refPtr false ptr) := by
    have entry : extras[slot] = .refPtr false ptr := by simpa [holEl_eq_getElem slot extras bound] using pointer
    have fullBound : slot < (extras ++ env).length := by simp; omega
    have entryFull : (extras ++ env)[slot] = .refPtr false ptr := by
      simpa [List.getElem_append_left, bound] using entry
    change (extras ++ env)[slot]? = some (.refPtr false ptr)
    exact List.getElem?_eq_some_iff.mpr ⟨fullBound, entryFull⟩
  have smallIdx : BackendCommon.smallEnoughInt (Int.ofNat idx) := by simpa [index] using small
  have updateRun := evaluate_update_const (slot + 1) idx ptr oldTag oldLeft oldRight initial (.refPtr false fresh)
    (.refPtr false fresh :: extras ++ env) allocated ptrAt (by simp) index smallIdx allocatedFound
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
  rw [shiftBlock, workerAuxSource.eq_def]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate,
    evaluate_shifted_mutCons tag left right extras env state leftWf rightWf]
  dsimp only
  simp only [List.singleton_append]
  dsimp only [allocated, fresh, newBlock] at updateRun
  simp only [List.cons_append] at updateRun
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, updateRun]
  dsimp only
  simp only [List.singleton_append, shiftBlock_add, Nat.add_comm 2 extras.length, shiftVars, List.length_map]
  dsimp only [fresh, newBlock] at mapComm
  rw [mapComm]
  rfl

/-- Flapjack infrastructure: the auxiliary constructor case follows from the
child's auxiliary induction hypothesis. This omits the original measure and
the other conclusions of the full call-block simulation. -/
theorem evaluate_aux_frame_core {C F : Type} (loc dest tag : Nat) (left right : List Nat) (child : CallBlock)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 extras : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (oldRefs : HolFiniteMapExact Nat (Ref Value))
    (slot idx ptr : Nat) (initial : Value) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [callBlockToBvi loc (.callBlock tag left child right)] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel opt f env1 env2)
    (states : stateRel f source target) (wf : wfBlock env1.length (.callBlock tag left child right))
    (oldDomain : oldRefs.domain ⊆ target.refs.domain)
    (hole : CallBlockEnvironment.allocHoleHasVal f target.refs extras slot idx initial)
    (pointer : holEl slot extras = .refPtr false ptr)
    (childIH : ∀ childResult mid linked,
      evaluate [callBlockToBvi loc child] env1 source = (childResult, mid) →
      childResult ≠ .err (.abort .typeError) → stateRel f source { target with refs := linked } →
      oldRefs.domain ⊆ linked.domain →
      CallBlockEnvironment.allocHoleHasVal f linked
        (unitValue :: .refPtr false (leastUnusedRef target.refs) :: extras) 1 right.length (.number 0) →
      AuxCore child dest env2 { target with refs := linked } f oldRefs
        (unitValue :: .refPtr false (leastUnusedRef target.refs) :: extras)
        1 right.length (leastUnusedRef target.refs) childResult mid) :
    AuxCore (.callBlock tag left child right) dest env2 target f oldRefs extras slot idx ptr result final := by
  have targetLength := envRel_length opt f env1 env2 environments
  have targetLeft := wfVars_expand env1.length env2.length left wf.1 targetLength
  have targetRight := wfVars_expand env1.length env2.length right wf.2.2.1 targetLength
  have small : BackendCommon.smallEnoughInt (Int.ofNat (right.map (fun n => holEl n env2)).reverse.length) := by
    simpa using wf.2.2.2
  obtain ⟨oldTag, oldLeft, oldRight, oldFound, different, linkedHeaps, newHole, domain, _, _⟩ :=
    link_frame_invariants f source.refs target.refs extras slot ptr idx tag
      (right.map (fun n => holEl n env2)).reverse (left.map (fun n => holEl n env2)).reverse
      initial states.1 hole pointer small
  obtain ⟨tag', left', right', found', frameRun⟩ :=
    evaluate_aux_frame tag dest slot idx ptr left right child extras env2 target f initial targetLeft targetRight hole pointer
  rw [oldFound] at found'
  simp only [Option.some.injEq, Ref.mutBlock.injEq] at found'
  obtain ⟨rfl, _, rfl, _, rfl⟩ := found'
  let linked := (target.refs.updateEq (ptr,
    .mutBlock oldTag false oldLeft (.refPtr false (leastUnusedRef target.refs)) oldRight)).updateEq
      (leastUnusedRef target.refs, .mutBlock tag false (right.map (fun n => holEl n env2)).reverse (.number 0)
        (left.map (fun n => holEl n env2)).reverse)
  have childStates : stateRel f source { target with refs := linked } := ⟨linkedHeaps, states.2⟩
  have childDomain : oldRefs.domain ⊆ linked.domain := fun key present => domain (oldDomain present)
  have newHole' : CallBlockEnvironment.allocHoleHasVal f linked
      (unitValue :: .refPtr false (leastUnusedRef target.refs) :: extras) 1 right.length (.number 0) := by
    simpa using newHole
  rw [CallBlockFrame.evaluate_frame loc tag left right child env1 source wf.1 wf.2.2.1] at run
  cases childRun : evaluate [callBlockToBvi loc child] env1 source with
  | mk childResult mid =>
    have childSafe : childResult ≠ .err (.abort .typeError) := by
      intro bad
      subst childResult
      simp [childRun] at run
      exact notTypeError run.1.symm
    obtain ⟨targetResult, next, g, childTargetRun, related, nextStates, extension, fresh, unchanged, still, success⟩ :=
      childIH childResult mid linked childRun childSafe childStates childDomain newHole'
    have targetRun : evaluate [workerAuxSource (shiftBlock extras.length (.callBlock tag left child right)) dest slot idx]
        (extras ++ env2) target = (targetResult, next) := by
      rw [frameRun]
      simpa [AuxCore, List.cons_append] using childTargetRun
    have invariants := linked_frame_return_invariants f g target.refs next.refs ptr oldTag tag oldLeft oldRight
      (right.map (fun n => holEl n env2)).reverse (left.map (fun n => holEl n env2)).reverse
      initial oldFound fresh unchanged still
    have returnedHole := linked_frame_old_hole f target.refs next.refs extras slot ptr idx oldTag tag oldLeft oldRight
      (right.map (fun n => holEl n env2)).reverse (left.map (fun n => holEl n env2)).reverse
      initial hole pointer oldFound unchanged still
    cases childResult with
    | err error =>
      simp [childRun] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      exact ⟨targetResult, next, g, targetRun, related, nextStates, extension,
        invariants.1, invariants.2.1, invariants.2.2, by intro _ impossible; cases impossible⟩
    | val values =>
      obtain ⟨sourceValue, rfl⟩ := evaluate_singleton _ env1 source mid values childRun
      obtain ⟨targetValue, childBlocks, childHole⟩ := success sourceValue rfl
      have newHoleNext := CallBlockAllocation.alloc_hole_advance f g linked next.refs
        (unitValue :: .refPtr false (leastUnusedRef target.refs) :: extras) 1 right.length (.number 0) targetValue
        newHole' childHole fresh
      have singleHole := CallBlockWorkerLeaf.alloc_hole_reindex g next.refs
        (unitValue :: .refPtr false (leastUnusedRef target.refs) :: extras) [.refPtr false (leastUnusedRef target.refs)]
        1 0 right.length (leastUnusedRef target.refs) targetValue newHoleNext
        (by simp [holEl, holHd]) (by simp) (by simp [holEl, holHd])
      have leftRelated := CallBlockEnvironment.wfVars_list_rel left opt f env1 env2 environments wf.1
      have rightRelated := CallBlockEnvironment.wfVars_list_rel right opt f env1 env2 environments wf.2.2.1
      have leftNext := listRel_submap f g _ _ leftRelated extension
      have rightNext := listRel_submap f g _ _ rightRelated extension
      have freshOutside := fresh_not_in_range f source.refs target.refs states.1
      have blocks := linked_frame_block_relation f g oldRefs target.refs next.refs ptr oldTag tag oldLeft oldRight
        (right.map (fun n => holEl n env2)).reverse (left.map (fun n => holEl n env2)).reverse
        (right.map (fun n => holEl n env1)).reverse (left.map (fun n => holEl n env1)).reverse
        sourceValue targetValue returnedHole.2 different oldDomain freshOutside unchanged
        (by simpa using singleHole) childBlocks (reverse_related g rightNext) (reverse_related g leftNext)
      simp [childRun, holHd] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      refine ⟨targetResult, next, g, targetRun, ?_, nextStates, extension,
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
        exact ⟨.refPtr false (leastUnusedRef target.refs), by simpa using blocks, returnedHole.1⟩

end Flapjack.Compiler.Backend.BviTmc.CallBlockAuxFrame
