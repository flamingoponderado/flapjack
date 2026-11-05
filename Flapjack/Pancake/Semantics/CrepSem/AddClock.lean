import Flapjack.Pancake.Semantics.CrepSem.EventsMono

/-!
# Clock-shift infrastructure for the exact Crep evaluator

FLAPJACK-SPECIFIC (untagged) infrastructure for HOL
`crepPropsScript.sml:1020 evaluate_add_clock_io_events_mono` and its underlying
`crepPropsScript.sml:886 evaluate_add_clock_eq`.

The public tagged theorem is
`Flapjack.crepPropsEvaluateAddClockIoEventsMono` in the `crepPropsScript.sml`
counterpart `CrepProps.lean`.  Everything here is Flapjack-internal plumbing:
the state shift `crepStateAddClock`, its commutation with the exact state
updates, the shared-memory commutation helpers, and the combined
event-prefix/clock-shift predicate `CrepAddClockCombined`.

STATUS (bead `flapjack-2de.3`): this module deliberately stops at the helper
layer.  A faithful kernel-checked proof of
`evaluate_add_clock_io_events_mono` on the exact Crep evaluator needs HOL
`evaluate_add_clock_eq` (`crepPropsScript.sml:886`): in the `Seq`/`Dec`/`Call`
clauses the high-clock run's intermediate state must be identified with the
original run's intermediate state with its clock raised, and the event-prefix
computation alone cannot supply that.  `evaluate_add_clock_eq` is the separate,
still-open port `flapjack-2de.2`, so `flapjack-2de.3` is blocked on it.  No
declaration here carries an `@[hol]` tag.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- Add `extra` to the clock of an exact Crep state. -/
abbrev crepStateAddClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (extra : Nat) : CrepSemHOLState width σ :=
  { state with clock := state.clock + extra }

@[simp] theorem crepStateAddClock_clock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (extra : Nat) :
    (crepStateAddClock state extra).clock = state.clock + extra := rfl

@[simp] theorem crepStateAddClock_locals {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (extra : Nat) :
    (crepStateAddClock state extra).locals = state.locals := rfl

@[simp] theorem crepStateAddClock_globals {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (extra : Nat) :
    (crepStateAddClock state extra).globals = state.globals := rfl

@[simp] theorem crepStateAddClock_code {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (extra : Nat) :
    (crepStateAddClock state extra).code = state.code := rfl

@[simp] theorem crepStateAddClock_memory {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (extra : Nat) :
    (crepStateAddClock state extra).memory = state.memory := rfl

@[simp] theorem crepStateAddClock_memaddrs {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (extra : Nat) :
    (crepStateAddClock state extra).memaddrs = state.memaddrs := rfl

@[simp] theorem crepStateAddClock_shMemaddrs {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (extra : Nat) :
    (crepStateAddClock state extra).shMemaddrs = state.shMemaddrs := rfl

@[simp] theorem crepStateAddClock_be {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (extra : Nat) :
    (crepStateAddClock state extra).be = state.be := rfl

@[simp] theorem crepStateAddClock_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (extra : Nat) :
    (crepStateAddClock state extra).ffi = state.ffi := rfl

@[simp] theorem crepStateAddClock_baseAddr {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (extra : Nat) :
    (crepStateAddClock state extra).baseAddr = state.baseAddr := rfl

@[simp] theorem crepStateAddClock_topAddr {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (extra : Nat) :
    (crepStateAddClock state extra).topAddr = state.topAddr := rfl

@[simp] theorem crepStateAddClock_zero {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) : crepStateAddClock state 0 = state := by
  unfold crepStateAddClock
  simp only [Nat.add_zero]

@[simp] theorem setVar_crepStateAddClock {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (value : HolWordLab width) (state : CrepSemHOLState width σ)
    (extra : Nat) :
    CrepSemHOLState.setVar name value (crepStateAddClock state extra) =
      crepStateAddClock (CrepSemHOLState.setVar name value state) extra := rfl

@[simp] theorem setGlobals_crepStateAddClock {width : Nat} [NeZero width] {σ : Type}
    (key : BitVec 5) (value : HolWordLab width) (state : CrepSemHOLState width σ)
    (extra : Nat) :
    CrepSemHOLState.setGlobals key value (crepStateAddClock state extra) =
      crepStateAddClock (CrepSemHOLState.setGlobals key value state) extra := rfl

@[simp] theorem emptyLocals_crepStateAddClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (extra : Nat) :
    CrepSemHOLState.emptyLocals (crepStateAddClock state extra) =
      crepStateAddClock (CrepSemHOLState.emptyLocals state) extra := rfl

/-- The exact expression evaluator is insensitive to the clock shift. -/
@[simp] theorem evalCrepSemHOLExp_crepStateAddClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (expression : CrepExpHOL width) (extra : Nat) :
    evalCrepSemHOLExp (crepStateAddClock state extra) expression =
      evalCrepSemHOLExp state expression := by
  change evalCrepSemHOLExp { state with clock := state.clock + extra } expression =
    evalCrepSemHOLExp state expression
  fun_induction evalCrepSemHOLExp state expression with
  | case7 _ args ih | case8 _ args ih =>
      simp only [evalCrepSemHOLExp]
      rw [optMmapCongHOL args args _ _ rfl ih]
  | _ => simp_all [evalCrepSemHOLExp]

/-- The combined clock-shift statement: the two runs share an event prefix, and
if the original did not time out then the shifted run is exactly the original
run with its final clock raised by `extra` (HOL `evaluate_add_clock_eq`). -/
abbrev CrepAddClockCombined {width : Nat} [NeZero width] {σ : Type}
    (program : CrepProgHOL width) (state : CrepSemHOLState width σ) (extra : Nat) : Prop :=
  (evalCrepSemHOLProgExact state program).2.ffi.ioEvents <+:
    (evalCrepSemHOLProgExact (crepStateAddClock state extra) program).2.ffi.ioEvents ∧
  ((evalCrepSemHOLProgExact state program).1 ≠ some .timeOut →
    evalCrepSemHOLProgExact (crepStateAddClock state extra) program =
      ((evalCrepSemHOLProgExact state program).1,
        crepStateAddClock (evalCrepSemHOLProgExact state program).2 extra))

end Flapjack
