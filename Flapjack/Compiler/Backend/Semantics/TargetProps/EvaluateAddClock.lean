import Mathlib.Tactic.SplitIfs
import Flapjack.Compiler.Backend.Semantics.TargetSem.Evaluate

namespace Flapjack

set_option maxHeartbeats 1200000 in
/-- Full target evaluator stability after increasing a clock that already
returned a non-TimeOut result. The only run and side condition are HOL's own. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateTargetAddClock {width : Nat} [NeZero width]
    {state projection : Type} {σ : Type} (mc : MachineConfig width state projection)
    (ffi : HolFfiState σ) (k : Nat) (ms : state) (extra : Nat)
    (result : MachineResult) (ms1 : state) (ffi1 : HolFfiState σ)
    (h : evaluateTargetHOL mc ffi k ms = (result, ms1, ffi1))
    (hnt : result ≠ .timeOut) :
    evaluateTargetHOL mc ffi (k + extra) ms = (result, ms1, ffi1) := by
  induction k generalizing mc ffi ms result ms1 ffi1 with
  | zero =>
    simp only [evaluateTargetHOL, Prod.mk.injEq] at h
    exact False.elim (hnt h.1.symm)
  | succ k ih =>
    simp only [Nat.succ_add, evaluateTargetHOL] at h ⊢
    try dsimp only at h ⊢
    repeat' (first
      | exact ih _ _ _ _ _ _ h hnt
      | exact h
      | split at h <;> (try simp_all [-ih])
      | cases ‹Compiler.Encoders.Asm.HolAddr width› <;> (try simp_all [-ih])
      | split <;> (try simp_all [-ih]))

    all_goals try split_ifs at h ⊢
    all_goals grind only [Prod.mk.injEq]

end Flapjack
