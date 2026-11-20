module

public import Flapjack.Compiler.Backend.Semantics.BviSem.State
public import Lean.Elab.Tactic.Omega

@[expose] public section

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

/-- Increasing the clock leaves the code unchanged. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "inc_clock_code"
  (fmap_as_finite_support := [refs])]
theorem incClock_code {C F : Type} (n : Nat) (s : BviSem.BviState C F) :
    (incClock n s).code = s.code := rfl

/-- Increasing the clock leaves the reference store unchanged. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "inc_clock_refs"
  (fmap_as_finite_support := [refs])]
theorem incClock_refs {C F : Type} (n : Nat) (s : BviSem.BviState C F) :
    (incClock n s).refs = s.refs := rfl

/-- Increasing the clock leaves the global pointer unchanged. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "inc_clock_global"
  (fmap_as_finite_support := [refs])]
theorem incClock_global {C F : Type} (n : Nat) (s : BviSem.BviState C F) :
    (incClock n s).global = s.global := rfl

/-- Increasing the clock leaves the FFI state unchanged. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "inc_clock_ffi"
  (fmap_as_finite_support := [refs])]
theorem incClock_ffi {C F : Type} (n : Nat) (s : BviSem.BviState C F) :
    (incClock n s).ffi = s.ffi := rfl

/-- Increasing the clock adds to the stored clock. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "inc_clock_clock"
  (fmap_as_finite_support := [refs])]
theorem incClock_clock {C F : Type} (n : Nat) (s : BviSem.BviState C F) :
    (incClock n s).clock = s.clock + n := rfl

/-- Decreasing the clock leaves the global pointer unchanged. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "dec_clock_global"
  (fmap_as_finite_support := [refs])]
theorem decClock_global {C F : Type} (n : Nat) (s : BviSem.BviState C F) :
    (BviSem.decClock n s).global = s.global := rfl

/-- Decreasing the clock leaves the FFI state unchanged. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "dec_clock_ffi"
  (fmap_as_finite_support := [refs])]
theorem decClock_ffi {C F : Type} (n : Nat) (s : BviSem.BviState C F) :
    (BviSem.decClock n s).ffi = s.ffi := rfl

/-- Decreasing the clock leaves the reference store unchanged. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "dec_clock_refs"
  (fmap_as_finite_support := [refs])]
theorem decClock_refs {C F : Type} (n : Nat) (s : BviSem.BviState C F) :
    (BviSem.decClock n s).refs = s.refs := rfl

/-- Decreasing the clock commutes with replacing the code. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "dec_clock_with_code"
  (fmap_as_finite_support := [refs])]
theorem decClock_with_code {C F : Type} (n : Nat) (s : BviSem.BviState C F)
    (c : Spt (Nat × Bvi.Exp)) :
    BviSem.decClock n { s with code := c } = { BviSem.decClock n s with code := c } := by
  cases s
  rfl

/-- Decreasing the clock leaves the code unchanged. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "dec_clock_code"
  (fmap_as_finite_support := [refs])]
theorem decClock_code {C F : Type} (n : Nat) (s : BviSem.BviState C F) :
    (BviSem.decClock n s).code = s.code := rfl

/-- A zero decrement leaves the state unchanged.  HOL's `n` is free and
    unused, so it keeps an independent type. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "dec_clock0"
  (fmap_as_finite_support := [refs])]
theorem decClock_zero {α γ F : Type} (_n : α) (s : BviSem.BviState γ F) :
    BviSem.decClock 0 s = s := by
  cases s
  simp [BviSem.decClock]

/-- An increment result has clock zero exactly when the state's clock is zero
    and the increment is zero. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "inc_clock_eq_0"
  (fmap_as_finite_support := [refs])]
theorem incClock_eq_zero {C F : Type} (extra : Nat) (s : BviSem.BviState C F) :
    (incClock extra s).clock = 0 ↔ s.clock = 0 ∧ extra = 0 := by
  simp [incClock]

/-- One decrement of a nonzero increment gives the previous clock. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "dec_clock_1_inc_clock"
  (fmap_as_finite_support := [refs])]
theorem decClock_one_incClock {C F : Type} (x : Nat) (s : BviSem.BviState C F)
    (nonzero : x ≠ 0) :
    BviSem.decClock 1 (incClock x s) = incClock (x - 1) s := by
  cases s
  simp only [incClock, BviSem.decClock] at *
  congr 1
  omega

/-- One decrement commutes with an increment when the clock is nonzero.  HOL
    states this a second time as `dec_clock_1_inc_clock2`, identical to
    `dec_clock_inv_clock1` up to variable names; the twin keeps that separate
    declaration. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "dec_clock_1_inc_clock2"
  (fmap_as_finite_support := [refs])]
theorem decClock_one_incClock_comm {C F : Type} (x : Nat) (s : BviSem.BviState C F)
    (nonzero : s.clock ≠ 0) :
    BviSem.decClock 1 (incClock x s) = incClock x (BviSem.decClock 1 s) := by
  cases s
  simp only [incClock, BviSem.decClock] at *
  congr 1
  omega

/-- A decrement that does not exhaust the clock commutes with an increment. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "dec_clock_inc_clock"
  (fmap_as_finite_support := [refs])]
theorem decClock_incClock_enough {C F : Type} (n x : Nat) (s : BviSem.BviState C F)
    (enough : ¬ s.clock < n) :
    BviSem.decClock n (incClock x s) = incClock x (BviSem.decClock n s) := by
  cases s
  simp only [incClock, BviSem.decClock] at *
  congr 1
  omega

end Flapjack.Compiler.Backend.BviProps
