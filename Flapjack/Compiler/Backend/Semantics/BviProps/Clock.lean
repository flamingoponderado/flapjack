import Flapjack.Compiler.Backend.Semantics.BviSem.State
import Lean.Elab.Tactic.Omega

/-! Clock extension for BVI evaluation. -/
namespace Flapjack.Compiler.Backend.BviProps

/-- Canonical BVI reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness

/-- Add an evaluation-clock allowance. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "inc_clock_def"
  (fmap_as_finite_support := [refs])]
def incClock {C F : Type} (n : Nat) (s : BviSem.BviState C F) : BviSem.BviState C F :=
  { s with clock := s.clock + n }

/-- A zero allowance does not change the state. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "inc_clock_ZERO"
  (fmap_as_finite_support := [refs])]
theorem incClock_zero {C F : Type} (s : BviSem.BviState C F) : incClock 0 s = s := by
  cases s
  simp [incClock]

/-- Two clock allowances combine by addition. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "inc_clock_ADD"
  (fmap_as_finite_support := [refs])]
theorem incClock_add {C F : Type} (n m : Nat)
    (s : Flapjack.Compiler.Backend.BviSem.BviState C F) :
    incClock n (incClock m s) = incClock (n + m) s := by
  cases s
  simp [incClock, Nat.add_comm, Nat.add_left_comm]

/-- Decrementing an available call budget commutes with an added allowance. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "dec_clock_inv_clock"
  (fmap_as_finite_support := [refs])]
theorem decClock_incClock {C F : Type} (s : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (ticks extra : Nat) (available : ¬s.clock < ticks + 1) :
    BviSem.decClock (ticks + 1) (incClock extra s) =
      incClock extra (BviSem.decClock (ticks + 1) s) := by
  cases s
  simp only [incClock, BviSem.decClock] at *
  congr 1
  omega

/-- Decrementing a nonzero clock commutes with an added allowance. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "dec_clock_inv_clock1"
  (fmap_as_finite_support := [refs])]
theorem decClock_incClock_one {C F : Type} (s : BviSem.BviState C F) (extra : Nat)
    (nonzero : s.clock ≠ 0) :
    BviSem.decClock 1 (incClock extra s) = incClock extra (BviSem.decClock 1 s) := by
  cases s
  simp only [incClock, BviSem.decClock] at *
  congr 1
  omega

end Flapjack.Compiler.Backend.BviProps
