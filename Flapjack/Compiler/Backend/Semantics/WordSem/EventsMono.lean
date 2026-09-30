import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
import Flapjack.FfiHOL

/-!
# WordSem FFI event-prefix support

This is proof-side infrastructure for the exact HOL
`wordPropsScript.sml:evaluate_io_events_mono` port.  It records the local
shared-memory and external-call facts needed by the evaluator induction; the
tagged theorem itself will live under this WordSem counterpart module. -/

namespace Flapjack

namespace WordSemStateFiniteExact

private theorem shMemStore_ioEvents_prefix {width : Nat} [NeZero width]
    {rw : Nat} [NeZero rw] {C F : Type} (address value : BitVec width)
    (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+: (shMemStore (rw := rw) address value state).2.ffi.ioEvents := by
  by_cases hdom : state.shMdomain address
  · simp only [shMemStore, if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedWrite) [0]
        (panWordToBytesHOL value false ++ panWordToBytesHOL address false) with
    | final _ => simp [flushState]
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedWrite) [0]
          (panWordToBytesHOL value false ++ panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [shMemStore, hdom]

private theorem shMemStoreByte_ioEvents_prefix {width : Nat} [NeZero width]
    {rw : Nat} [NeZero rw] {C F : Type} (address value : BitVec width)
    (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+: (shMemStoreByte (rw := rw) address value state).2.ffi.ioEvents := by
  by_cases hdom : state.shMdomain (riscvByteAlignHOL address)
  · simp only [shMemStoreByte, if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedWrite) [1]
        ([getByteHOL8 0 value false] ++ panWordToBytesHOL address false) with
    | final _ => simp [flushState]
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedWrite) [1]
          ([getByteHOL8 0 value false] ++ panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [shMemStoreByte, hdom]

private theorem shMemStore16_ioEvents_prefix {width : Nat} [NeZero width]
    {rw : Nat} [NeZero rw] {C F : Type} (address value : BitVec width)
    (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+: (shMemStore16 (rw := rw) address value state).2.ffi.ioEvents := by
  by_cases hdom : state.shMdomain (riscvByteAlignHOL address)
  · simp only [shMemStore16, if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedWrite) [2]
        ((panWordToBytesHOL value false).take 2 ++ panWordToBytesHOL address false) with
    | final _ => simp [flushState]
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedWrite) [2]
          ((panWordToBytesHOL value false).take 2 ++ panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [shMemStore16, hdom]

private theorem shMemStore32_ioEvents_prefix {width : Nat} [NeZero width]
    {rw : Nat} [NeZero rw] {C F : Type} (address value : BitVec width)
    (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+: (shMemStore32 (rw := rw) address value state).2.ffi.ioEvents := by
  by_cases hdom : state.shMdomain (riscvByteAlignHOL address)
  · simp only [shMemStore32, if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedWrite) [4]
        ((panWordToBytesHOL value false).take 4 ++ panWordToBytesHOL address false) with
    | final _ => simp [flushState]
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedWrite) [4]
          ((panWordToBytesHOL value false).take 4 ++ panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [shMemStore32, hdom]

private theorem shMemLoad_ioEvents_prefix {width : Nat} [NeZero width]
    {C F : Type} (address : BitVec width) (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+:
      (match shMemLoad address state with
       | none => state.ffi.ioEvents
       | some (.final _) => state.ffi.ioEvents
       | some (.ret nextFfi _) => nextFfi.ioEvents) := by
  unfold shMemLoad
  by_cases hdom : state.shMdomain address
  · simp only [if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedRead) [0]
        (panWordToBytesHOL address false) with
    | final _ => exact List.prefix_refl _
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedRead) [0] (panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [hdom]

private theorem shMemLoadByte_ioEvents_prefix {width : Nat} [NeZero width]
    {C F : Type} (address : BitVec width) (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+:
      (match shMemLoadByte address state with
       | none => state.ffi.ioEvents
       | some (.final _) => state.ffi.ioEvents
       | some (.ret nextFfi _) => nextFfi.ioEvents) := by
  unfold shMemLoadByte
  by_cases hdom : state.shMdomain (riscvByteAlignHOL address)
  · simp only [if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedRead) [1]
        (panWordToBytesHOL address false) with
    | final _ => exact List.prefix_refl _
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedRead) [1] (panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [hdom]

private theorem shMemLoad16_ioEvents_prefix {width : Nat} [NeZero width]
    {C F : Type} (address : BitVec width) (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+:
      (match shMemLoad16 address state with
       | none => state.ffi.ioEvents
       | some (.final _) => state.ffi.ioEvents
       | some (.ret nextFfi _) => nextFfi.ioEvents) := by
  unfold shMemLoad16
  by_cases hdom : state.shMdomain (riscvByteAlignHOL address)
  · simp only [if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedRead) [2]
        (panWordToBytesHOL address false) with
    | final _ => exact List.prefix_refl _
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedRead) [2] (panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [hdom]

private theorem shMemLoad32_ioEvents_prefix {width : Nat} [NeZero width]
    {C F : Type} (address : BitVec width) (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+:
      (match shMemLoad32 address state with
       | none => state.ffi.ioEvents
       | some (.final _) => state.ffi.ioEvents
       | some (.ret nextFfi _) => nextFfi.ioEvents) := by
  unfold shMemLoad32
  by_cases hdom : state.shMdomain (riscvByteAlignHOL address)
  · simp only [if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedRead) [4]
        (panWordToBytesHOL address false) with
    | final _ => exact List.prefix_refl _
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedRead) [4] (panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [hdom]

private theorem shMemSetVar_ioEvents_prefix {width rw : Nat} [NeZero width]
    [NeZero rw] {C F : Type} (result : Option (HolFfiResult F)) (v : Nat)
    (state : WordSemStateFiniteExact width C F)
    (hret : ∀ nextFfi bytes, result = some (.ret nextFfi bytes) →
      state.ffi.ioEvents <+: nextFfi.ioEvents) :
    state.ffi.ioEvents <+: (shMemSetVar (rw := rw) result v state).2.ffi.ioEvents := by
  cases result with
  | none => exact List.prefix_refl _
  | some result =>
      cases result with
      | final outcome => exact List.prefix_refl _
      | ret nextFfi bytes =>
          simpa [shMemSetVar, setVar] using hret nextFfi bytes rfl

private theorem shareInst_ioEvents_prefix {width rw : Nat} [NeZero width]
    [NeZero rw] {C F : Type} (operator : WordMemOp) (v : Nat)
    (address : BitVec width) (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+: (shareInst (rw := rw) operator v address state).2.ffi.ioEvents := by
  cases operator with
  | load =>
      simp only [shareInst]
      apply shMemSetVar_ioEvents_prefix (rw := rw) (v := v)
      intro nextFfi bytes hret
      have hload := shMemLoad_ioEvents_prefix address state
      rw [show shMemLoad address state = some (.ret nextFfi bytes) from hret] at hload
      exact hload
  | load8 =>
      simp only [shareInst]
      apply shMemSetVar_ioEvents_prefix (rw := rw) (v := v)
      intro nextFfi bytes hret
      have hload := shMemLoadByte_ioEvents_prefix address state
      rw [show shMemLoadByte address state = some (.ret nextFfi bytes) from hret] at hload
      exact hload
  | load16 =>
      simp only [shareInst]
      apply shMemSetVar_ioEvents_prefix (rw := rw) (v := v)
      intro nextFfi bytes hret
      have hload := shMemLoad16_ioEvents_prefix address state
      rw [show shMemLoad16 address state = some (.ret nextFfi bytes) from hret] at hload
      exact hload
  | load32 =>
      simp only [shareInst]
      apply shMemSetVar_ioEvents_prefix (rw := rw) (v := v)
      intro nextFfi bytes hret
      have hload := shMemLoad32_ioEvents_prefix address state
      rw [show shMemLoad32 address state = some (.ret nextFfi bytes) from hret] at hload
      exact hload
  | store =>
      simp only [shareInst]
      cases hvar : getVar v state with
      | none => simp
      | some value =>
          cases value with
          | word w => simpa [hvar] using shMemStore_ioEvents_prefix (rw := rw) address w state
          | loc _ _ => simp
  | store8 =>
      simp only [shareInst]
      cases hvar : getVar v state with
      | none => simp
      | some value =>
          cases value with
          | word w => simpa [hvar] using shMemStoreByte_ioEvents_prefix (rw := rw) address w state
          | loc _ _ => simp
  | store16 =>
      simp only [shareInst]
      cases hvar : getVar v state with
      | none => simp
      | some value =>
          cases value with
          | word w => simpa [hvar] using shMemStore16_ioEvents_prefix (rw := rw) address w state
          | loc _ _ => simp
  | store32 =>
      simp only [shareInst]
      cases hvar : getVar v state with
      | none => simp
      | some value =>
          cases value with
          | word w => simpa [hvar] using shMemStore32_ioEvents_prefix (rw := rw) address w state
          | loc _ _ => simp

private theorem cutState_ioEvents_eq {width : Nat} [NeZero width]
    {C F : Type} {names : WordLangCutsetsHOL}
    {state next : WordSemStateFiniteExact width C F}
    (h : cutState names state = some next) : next.ffi.ioEvents = state.ffi.ioEvents := by
  unfold cutState at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    cases h
    rfl

private theorem memStore_ioEvents_eq {width : Nat} [NeZero width] {C F : Type}
    (address : BitVec width) (value : WordLocW width)
    (state : WordSemStateFiniteExact width C F) :
    (memStore address value state).map (fun next => next.ffi.ioEvents) =
      (memStore address value state).map (fun _ => state.ffi.ioEvents) := by
  unfold memStore
  split <;> rfl

private theorem jumpExc_ioEvents_eq_of_some {width : Nat} [NeZero width] {C F : Type}
    (state next : WordSemStateFiniteExact width C F) (l1 l2 : Nat)
    (h : jumpExc state = some (next, l1, l2)) :
    next.ffi.ioEvents = state.ffi.ioEvents := by
  unfold jumpExc at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

private theorem gc_ioEvents_eq {width : Nat} [NeZero width] {C F : Type}
    (state next : WordSemStateFiniteExact width C F)
    (h : gc state = some next) : next.ffi.ioEvents = state.ffi.ioEvents := by
  simp only [gc] at h
  cases hfun : state.gcFun
      (wordSemEncStack state.stack, state.memory, state.mdomain, state.store) with
  | none => simp [hfun] at h
  | some result =>
      obtain ⟨wl, memory, store⟩ := result
      cases hdec : wordSemDecStack wl state.stack with
      | none => simp [hfun, hdec] at h
      | some stack =>
          simp only [hfun, hdec, Option.some.injEq] at h
          cases h
          rfl

private theorem popEnv_ioEvents_eq {width : Nat} [NeZero width] {C F : Type}
    (state next : WordSemStateFiniteExact width C F)
    (h : popEnv state = some next) : next.ffi.ioEvents = state.ffi.ioEvents := by
  cases hstack : state.stack with
  | nil => simp [popEnv, hstack] at h
  | cons frame frames =>
      cases frame with
      | stackFrame localsSize locals0 locals handler =>
          cases handler with
          | none =>
              simp [popEnv, hstack] at h
              cases h
              rfl
          | some handler =>
              simp [popEnv, hstack] at h
              cases h
              rfl

private theorem alloc_ioEvents_eq {width : Nat} [NeZero width] {C F : Type}
    (w : BitVec width) (names : WordLangCutsetsHOL)
    (state : WordSemStateFiniteExact width C F) :
    (alloc w names state).2.ffi.ioEvents = state.ffi.ioEvents := by
  unfold alloc
  split
  · simp [flushState]
  · rename_i envs hcut
    cases hgc : gc (pushEnv envs none (setStore .allocSize (.word w) state)) with
    | none => simp [flushState]
    | some g =>
      have hg := gc_ioEvents_eq _ _ hgc
      have hgin : (pushEnv envs none (setStore .allocSize (.word w) state)).ffi.ioEvents =
          state.ffi.ioEvents := rfl
      rw [hgin] at hg
      cases hp : popEnv g with
      | none => simp [hp, hg, flushState]
      | some p =>
        have hpop := popEnv_ioEvents_eq _ _ hp
        rw [hg] at hpop
        cases hstore : getStore .allocSize p with
        | none => simp [hp, hstore, hpop]
        | some space =>
          cases hspace : hasSpace space p with
          | none => simp [hp, hstore, hspace, hpop]
          | some fits => cases fits <;> simp [hp, hstore, hspace, hpop, flushState]

private theorem ffiStatement_ioEvents_prefix {width : Nat} [NeZero width]
    {C F : Type} (ffiIndex : Flapjack.Basis.Pure.MlString.MlString)
    (ptr1 len1 ptr2 len2 : Nat)
    (names : WordLangCutsetsHOL) (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+: (evaluate (.ffi ffiIndex ptr1 len1 ptr2 len2 names) state).2.ffi.ioEvents := by
  unfold evaluate
  repeat' split
  all_goals (try exact List.prefix_refl _)
  all_goals
    first
    | exact callFFIHOL_result_ioEvents_prefix _ _ _ _ _ (by assumption)
    | (rename_i hcall; exact callFFIHOL_result_ioEvents_prefix _ _ _ _ _ hcall)

end WordSemStateFiniteExact

end Flapjack
