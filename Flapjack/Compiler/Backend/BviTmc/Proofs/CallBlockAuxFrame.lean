import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockAllocation
import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockWorkerLeaf

/-! Nested mutable frames in auxiliary call-block simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallBlockAuxFrame
open BviTmc BviSem BvlSem

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
  refine ⟨oldTag, oldLeft, oldRight, ?_⟩
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

end Flapjack.Compiler.Backend.BviTmc.CallBlockAuxFrame
