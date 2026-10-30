import Flapjack.Compiler.Backend.Semantics.BviSem.State

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

end Flapjack.Compiler.Backend.BviProps
