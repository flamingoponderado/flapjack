import Flapjack.Compiler.Backend.Semantics.TargetProps.InterferenceSequence

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Literal source354: every successful clocked search preserves the target,
callee-saved register list and pointer register of the configuration. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem findNextInterferenceConst {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (k : Nat) (mc : MachineConfig width S Q)
    (ffi : HolFfiState σ) (ms : S) (app : InterferenceApp width S)
    (mc' : MachineConfig width S Q) (ffi' : HolFfiState σ)
    (h : findNextInterference mc ffi k ms = some (app, mc', ffi')) :
    mc'.target = mc.target ∧ mc'.calleeSavedRegs = mc.calleeSavedRegs ∧
      mc'.ptrReg = mc.ptrReg := by
  induction k generalizing mc ffi ms with
  | zero => simp [findNextInterference] at h
  | succ k ih =>
    simp only [findNextInterference] at h
    split at h
    · split at h
      · split at h
        · simpa using ih _ _ _ h
        · cases h
      · cases h
    · repeat' first | split at h | cases h
      all_goals simp

/-- Literal source370: unbounded next-interference choice preserves the same
three fields, derived from its actual successful search witness. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem nextInterferenceConst {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc : MachineConfig width S Q)
    (ffi : HolFfiState σ) (ms : S) (app : InterferenceApp width S)
    (mc' : MachineConfig width S Q) (ffi' : HolFfiState σ)
    (h : nextInterference mc ffi ms = some (app, mc', ffi')) :
    mc'.target = mc.target ∧ mc'.calleeSavedRegs = mc.calleeSavedRegs ∧
      mc'.ptrReg = mc.ptrReg := by
  obtain ⟨k, hk⟩ := holOptionSome_some
    (P := fun res => ∃ k, findNextInterference mc ffi k ms = some res) h
  exact findNextInterferenceConst k mc ffi ms app mc' ffi' hk

end Flapjack.Compiler.Backend.Semantics.TargetProps
