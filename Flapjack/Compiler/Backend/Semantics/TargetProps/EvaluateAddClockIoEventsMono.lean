import Mathlib.Logic.Basic
import Mathlib.Tactic.CasesM
import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateIoEventsMono

namespace Flapjack

set_option maxHeartbeats 1200000 in
/-- Clock-order event monotonicity over the full literal evaluator.
The only premise is clock order. Both runs use the same literal machine and FFI
transitions; the zero-clock case uses input-event prefix preservation. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "evaluate_add_clock_io_events_mono" (words_as_type_indexed_bitvec)]
theorem evaluateTargetAddClockIoEventsMono {width : Nat} [NeZero width]
    {state projection : Type} {σ : Type} (mc : MachineConfig width state projection)
    (ffi : HolFfiState σ) (k : Nat) (ms : state) (k' : Nat) (hle : k ≤ k') :
    (evaluateTargetHOL mc ffi k ms).2.2.ioEvents <+:
      (evaluateTargetHOL mc ffi k' ms).2.2.ioEvents := by
  induction k generalizing mc ffi ms k' with
  | zero => simpa only [evaluateTargetHOL] using evaluateTargetIoEventsMono mc ffi k' ms
  | succ k ih =>
    cases k' with
    | zero => exact False.elim (Nat.not_succ_le_zero k hle)
    | succ n =>
      have hkn : k ≤ n := Nat.le_of_succ_le_succ hle
      generalize hsmall : evaluateTargetHOL mc ffi (k + 1) ms = small
      generalize hlarge : evaluateTargetHOL mc ffi (n + 1) ms = large
      simp only [evaluateTargetHOL] at hsmall hlarge
      repeat' (first
        | exact List.prefix_refl _
        | (rw [← hlarge]; exact List.prefix_refl _)
        | (rw [← hsmall, ← hlarge]; exact ih _ _ _ _ hkn)
        | (rename_i hguard; rw [if_pos hguard] at hlarge)
        | (simp_all only [not_not])
        | cases_type Compiler.Encoders.Asm.HolAddr
        | (simp only [ite_and] at hsmall hlarge)
        | split at hsmall <;> (try simp_all only [↓reduceIte]))

end Flapjack
