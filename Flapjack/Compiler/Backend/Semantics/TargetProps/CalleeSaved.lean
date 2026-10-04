import Flapjack.Compiler.Backend.Semantics.TargetProps.RegisterOracles

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Literal source634: every callee-saved register receives no oracle override. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem targetIoRegsCalleeSaved {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (ms : S) (k r : Nat) (name : HolFfiName)
    (h : r ∈ mc.calleeSavedRegs) : targetIoRegs mc ffi ms k name r = none := by
  unfold targetIoRegs
  split
  · rfl
  · split <;> simp [h]

/-- Literal source640: every callee-saved register receives no oracle override. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem targetCcRegsCalleeSaved {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (ms : S) (k r : Nat)
    (h : r ∈ mc.calleeSavedRegs) : targetCcRegs mc ffi ms k r = none := by
  unfold targetCcRegs
  split
  · rfl
  · split <;> simp [h]

end Flapjack.Compiler.Backend.Semantics.TargetProps
