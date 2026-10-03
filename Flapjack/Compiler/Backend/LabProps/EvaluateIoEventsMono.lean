import Flapjack.Compiler.Backend.LabSem.Evaluate

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabSem

/-- Flapjack transition infrastructure: every successful shared load preserves
all earlier events. This is an equation consequence, not a named HOL lemma. -/
private theorem shareMemLoad_events {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (address : HolAddr width) (s next : LabSem.State width C F)
    (size : Nat) (result : HolFfiResult F)
    (h : shareMemLoad register address s size = some (result, next)) :
    s.ffi.ioEvents <+: next.ffi.ioEvents := by
  unfold shareMemLoad at h
  cases ha : addrValue address s with
  | none => simp [ha] at h
  | some value =>
      simp only [ha] at h
      cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead)
          [BitVec.ofNat 8 size] (sharedMemoryWordBytes value) with
      | final outcome =>
          simp only [hc] at h
          repeat' first | split at h | simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]
          all_goals rcases h with ⟨rfl, rfl⟩; exact List.prefix_refl _
      | ret ffi bytes =>
          have hp := callFFIHOL_return_ioEvents_prefix _ _ _ _ _ _ hc
          simp only [hc] at h
          repeat' first | split at h | simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]
          all_goals rcases h with ⟨rfl, rfl⟩
          all_goals exact hp

/-- Flapjack transition infrastructure for successful shared stores, including
final FFI outcomes. No separately named HOL declaration owns this consequence. -/
private theorem shareMemStore_events {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (address : HolAddr width) (s next : LabSem.State width C F)
    (size : Nat) (result : HolFfiResult F)
    (h : shareMemStore register address s size = some (result, next)) :
    s.ffi.ioEvents <+: next.ffi.ioEvents := by
  unfold shareMemStore at h
  cases hr : s.regs register with
  | loc sec lab => simp [hr] at h
  | word word =>
      simp only [hr] at h
      cases ha : addrValue address s with
      | none => simp [ha] at h
      | some value =>
          simp only [ha] at h
          cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 size]
              ((if size = 0 then sharedMemoryWordBytes word
                else (sharedMemoryWordBytes word).take size) ++ sharedMemoryWordBytes value) with
          | final outcome =>
              simp only [hc] at h
              repeat' first | split at h | simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]
              all_goals rcases h with ⟨rfl, rfl⟩; exact List.prefix_refl _
          | ret ffi bytes =>
              have hp := callFFIHOL_return_ioEvents_prefix _ _ _ _ _ _ hc
              simp only [hc] at h
              repeat' first | split at h | simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]
              all_goals rcases h with ⟨rfl, rfl⟩
              all_goals exact hp

/-- Flapjack dispatch consequence for all eight native shared-memory operators;
this helper has no separately named HOL original. -/
private theorem shareMemOp_events {width : Nat} [NeZero width] {C F : Type}
    (operator : HolMemop) (register : Nat) (address : HolAddr width)
    (s next : LabSem.State width C F) (result : HolFfiResult F)
    (h : shareMemOp operator register address s = some (result, next)) :
    s.ffi.ioEvents <+: next.ffi.ioEvents := by
  cases operator <;> simp only [shareMemOp] at h
  all_goals first
    | exact shareMemLoad_events _ _ _ _ _ _ h
    | exact shareMemStore_events _ _ _ _ _ _ h

/-- Flapjack recursive form of the full event-prefix theorem, with no target
result premise. The tagged original theorem below supplies its result binders. -/
private theorem evaluate_events {width : Nat} [NeZero width] {C F : Type}
    (s : LabSem.State width C F) : s.ffi.ioEvents <+: (evaluate s).2.ffi.ioEvents := by
  fun_induction evaluate s
  all_goals simp_all only [incPc, decClock, updPc, updReg]
  all_goals try first | exact List.prefix_refl _ | assumption
  case case3 s _ instruction _ _ _ next _ ih =>
    have hffi : next.ffi = s.ffi := (asmInstConsts instruction s).2.2.2.1
    simpa only [hffi] using ih
  case case11 => exact shareMemOp_events _ _ _ _ _ _ (by assumption)
  case case12 =>
    apply List.IsPrefix.trans (shareMemOp_events _ _ _ _ _ _ (by assumption))
    assumption
  case case27 => simp_all +zetaDelta
  case case28 => split <;> simp_all +zetaDelta
  case case33 =>
    apply List.IsPrefix.trans (callFFIHOL_return_ioEvents_prefix _ _ _ _ _ _ (by assumption))
    assumption

/-- Full original event monotonicity for every result of the native evaluator.
All state/configuration/FFI carriers and result binders are unrestricted;
timeout, failure, final FFI outcomes and returning transitions are included.
The evaluator inherits the reviewed real rendering (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "evaluate_io_events_mono"
  (words_as_type_indexed_bitvec)]
theorem evaluateIoEventsMono {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s1 : Flapjack.Compiler.Backend.LabSem.State width C F) (r : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (heval : evaluate s1 = (r, s2)) : s1.ffi.ioEvents <+: s2.ffi.ioEvents := by
  simpa only [heval] using evaluate_events s1

end Flapjack.Compiler.Backend.LabProps
