module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.State
public import Flapjack.HolRef

@[expose] public section

/-! Closure-state clock projection and reset lemmas from the original
`closProps` script. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

/-- Closure states use the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Rewriting the clock to its current value leaves the closure state unchanged. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "with_same_clock"
  (fmap_as_finite_support := [refs, code])]
theorem withSameClock {C F : Type} (s : State C F) :
    { s with clock := s.clock } = s := by
  cases s
  rfl

/-- Clock decrement leaves the closure code map unchanged. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dec_clock_code"
  (fmap_as_finite_support := [refs, code])]
theorem decClock_code {C F : Type} (x : Nat) (y : State C F) :
    (decClock x y).code = y.code := by
  simp [decClock]

/-- Clock decrement leaves the FFI state unchanged. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dec_clock_ffi"
  (fmap_as_finite_support := [refs, code])]
theorem decClock_ffi {C F : Type} (x : Nat) (y : State C F) :
    (decClock x y).ffi = y.ffi := by
  simp [decClock]

/-- Clock decrement leaves the compilation oracle unchanged. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dec_clock_compile_oracle"
  (fmap_as_finite_support := [refs, code])]
theorem decClock_compileOracle {C F : Type} (n : Nat) (s : State C F) :
    (decClock n s).compileOracle = s.compileOracle := by
  simp [decClock]

/-- Clock decrement leaves the compiler callback unchanged. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "dec_clock_compile"
  (fmap_as_finite_support := [refs, code])]
theorem decClock_compile {C F : Type} (n : Nat) (s : State C F) :
    (decClock n s).compile = s.compile := by
  simp [decClock]

/-- Rewriting the clock to its current value leaves the closure state unchanged,
stated with the original's explicit quantifier. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "clock_lemmas"
  (fmap_as_finite_support := [refs, code])]
theorem clockLemmas {C F : Type} :
    ∀ s : State C F, { s with clock := s.clock } = s := by
  intro s
  cases s
  rfl

end Flapjack.Compiler.Backend.ClosProps
