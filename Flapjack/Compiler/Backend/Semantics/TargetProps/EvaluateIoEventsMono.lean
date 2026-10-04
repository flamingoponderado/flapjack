import Mathlib.Logic.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.CasesM
import Flapjack.Compiler.Backend.Semantics.TargetSem.Evaluate

namespace Flapjack

set_option maxHeartbeats 1200000 in
/-- Input event trace is retained as a prefix by every literal target run.
All machine/FFI/clock inputs are arbitrary, with no extra oracle or validity premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateTargetIoEventsMono {width : Nat} [NeZero width]
    {state projection : Type} {σ : Type} (mc : MachineConfig width state projection)
    (ffi : HolFfiState σ) (k : Nat) (ms : state) :
    ffi.ioEvents <+: (evaluateTargetHOL mc ffi k ms).2.2.ioEvents := by
  induction k generalizing mc ffi ms with
  | zero => simp [evaluateTargetHOL]
  | succ k ih =>
    generalize hout : evaluateTargetHOL mc ffi (k + 1) ms = out
    simp only [evaluateTargetHOL] at hout
    repeat' (first
      | (rw [← hout]; exact ih _ _ _)
      | (rw [← hout]; exact List.prefix_refl _)
      | (rename_i nf nb hcall
         rw [← hout]
         exact (callFFIHOL_return_ioEvents_prefix ffi _ _ _ nf nb hcall).trans (ih _ _ _))
      | cases_type Compiler.Encoders.Asm.HolAddr
      | (simp only [ite_and] at hout)
      | split at hout <;> (try simp_all only [↓reduceIte]))


end Flapjack
