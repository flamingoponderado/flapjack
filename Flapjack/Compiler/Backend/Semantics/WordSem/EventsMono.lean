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

end WordSemStateFiniteExact

end Flapjack
