import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSub1

/-!
# Parity for the exact `panProps` `evaluate_clock_sub1`

Kernel-checked application of the tagged
`panPropsEvaluateClockSub1HOLFinite` (HOL
`cakeml/pancake/semantics/panPropsScript.sml:1131-1138`) over the exact
`PanPropsEvalStateFiniteExact` carrier and the pair evaluator
`evaluateHOLFinitePair`.

This module is kernel proof-term instantiation of the tagged theorem, not a
direct original-HOL `EVAL` oracle comparison: no oracle row is fabricated here.
The fixtures instantiate the theorem on `Skip` (whose HOL equation is
`evaluate (Skip,s) = (NONE,s)`) and kernel-check the clock-subtraction
arithmetic of the statement.
-/

namespace Flapjack.Test.PanPropsEvaluateClockSub1Parity

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanPropsEvalStateFiniteExact

/-- `Skip` over the pair evaluator returns the unchanged state, matching HOL
    `evaluate_def`'s `evaluate (Skip,s) = (NONE,s)`. -/
theorem evaluateHOLFinitePair_skip {width : Nat} {σ : Type} [NeZero width]
    (s : PanPropsEvalStateFiniteExact width σ) :
    PanPropsEvalStateFiniteExact.evaluateHOLFinitePair s (.skip : ProgHOL width) =
      (none, s) := by
  simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
    PanSemStateFiniteExact.evaluateHOLFiniteState_skip]

/-- Kernel-checked instance of `evaluate_clock_sub1` with `p = Skip`,
    `res = NONE`, `st = t`, and `t'` the clock-raised state.  The conclusion
    reduces to `(ck + t.clock) - ck = t.clock`, exercising the exact clock
    arithmetic of the HOL statement. -/
theorem clockSub1SkipFixture {width : Nat} {σ : Type} [NeZero width]
    (s : PanPropsEvalStateFiniteExact width σ) (ck : Nat) :
    PanPropsEvalStateFiniteExact.evaluateHOLFinitePair s (.skip : ProgHOL width) =
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { { s with clock := ck + s.clock } with
          clock := ({ s with clock := ck + s.clock } :
            PanPropsEvalStateFiniteExact width σ).clock - ck }
        (.skip : ProgHOL width) :=
  panPropsEvaluateClockSub1HOLFinite .skip s none s { s with clock := ck + s.clock } ck
    ⟨evaluateHOLFinitePair_skip s, by simp, rfl⟩

/-- Concrete clock instance: raising `20` by `3` and subtracting `3` recovers
    `20`, the arithmetic the `Skip` fixture relies on. -/
theorem clockSub1ClockArithmetic (ck c : Nat) : (ck + c) - ck = c :=
  Nat.add_sub_cancel_left ck c

def clockSub1ClockGuard : Bool :=
  ((3 + 20) - 3 == 20) && ((7 + 0) - 7 == 0)

#guard clockSub1ClockGuard

def runChecks : IO Bool := do
  if clockSub1ClockGuard then
    IO.println "PASS panProps evaluate_clock_sub1 clock-subtraction arithmetic"
    pure true
  else
    IO.println "FAIL panProps evaluate_clock_sub1 clock-subtraction arithmetic"
    pure false

end Flapjack.Test.PanPropsEvaluateClockSub1Parity
