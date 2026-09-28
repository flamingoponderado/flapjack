import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.CrepProps.EvaluateAddClockIoEventsMono
import Flapjack.PanObservationalSemantics
import Flapjack.FfiHOL

/-!
# Pancake `crepSem.semantics`

Source reference: `cakeml/pancake/semantics/crepSemScript.sml:448-471`
(`semantics_def`).  HOL repeatedly evaluates `Call NONE start []` at
clock-indexed states `s with clock := k`, fails when some clock yields a
`TimeOut`/`FinalFFI`/`Return` result, chooses a successful `Return` or
`FinalFFI` witness, and otherwise returns the `build_lprefix_lub` of the
clock-indexed FFI-event prefixes.

This module provides the exact observational behaviour carrier and the
clock-indexed entry evaluation over the already-ported exact clocked evaluator
`evalCrepSemHOLProg` and the exact finite-support state `CrepSemHOLState`.

-- FLAPJACK-SPECIFIC (deviation to document, not an exact `@[hol]` port of
-- `crepSem$semantics_def`): the exact evaluator `evalCrepSemHOLProg` takes the
-- two domain-membership decision procedures as explicit arguments, and the
-- shared prefix-LUB construction `buildPanLprefixLub` carries an
-- `lprefix_chain` witness of the clock-indexed event family.  The
-- evaluator-derived chain is now supplied internally
-- (`crepEvaluateClock_ioEvents_lprefixChain`, from the exact add-clock
-- event-prefix property `crepPropsScript.sml:1020`), so `crepSemantics` no
-- longer takes a caller-supplied `divergenceChain` (the earlier deviation,
-- bead `flapjack-pxn.18.4.8.2`).  The remaining difference from HOL is the
-- explicit `memDec`/`shMemDec` arguments and the `LoopLprefixLub` witness
-- carrier versus HOL's total `build_lprefix_lub`.  No `@[hol]` tag is attached
-- pending coordinator review of those two representations.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- Outcome of a successful crepSem run, mirroring HOL `semantics`'s two
successful result cases: a `Return` gives `Success`, a `FinalFFI` gives the
`FFI_outcome` of its `final_event`. -/
inductive CrepSemanticOutcome where
  | success
  | ffi (outcome : HolFfiOutcome)
  deriving DecidableEq, Repr

/-- Observational behaviour of a crepSem program, mirroring the HOL `semantics`
result constructors (`Fail`/`Terminate`/`Diverge`).  The divergence case carries
the event family and its least upper bound, exactly as in HOL's
`build_lprefix_lub` construction. -/
inductive CrepBehaviour where
  | diverge (family : Nat → List HolIoEvent) (trace : PanLprefixLub family)
  | terminate (outcome : CrepSemanticOutcome) (events : List HolIoEvent)
  | fail

/-- HOL `semantics_def`'s entry program `Call NONE start []`. -/
def crepEntryProgram {width : Nat} [NeZero width] (start : MlString) :
    CrepProgHOL width :=
  .call none start []

/-- Clock-indexed entry evaluation `evaluate (Call NONE start [], s with clock := k)`,
returning the exact `(result option, state)` pair of HOL `evaluate`. -/
def crepEvaluateClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (start : MlString)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (clock : Nat) : Option (CrepResultHOLExact width) × CrepSemHOLState width σ :=
  evalCrepSemHOLProg { state with clock := clock } memDec shMemDec (crepEntryProgram start)

/-- The FFI event list of a clock-indexed evaluation result, i.e.
`(SND (evaluate (prog, s with clock := k))).ffi.io_events`. -/
def crepResultEvents {width : Nat} [NeZero width] {σ : Type}
    (pair : Option (CrepResultHOLExact width) × CrepSemHOLState width σ) :
    List HolIoEvent :=
  pair.2.ffi.ioEvents

/-- HOL `semantics_def`'s successful-result outcome mapping:
`SOME (Return _) => Success`, `SOME (FinalFFI e) => FFI_outcome e`, else none. -/
def crepResultOutcome {width : Nat} [NeZero width] :
    Option (CrepResultHOLExact width) → Option CrepSemanticOutcome
  | some (.return _) => some .success
  | some (.finalFfi event) => some (.ffi event.outcome)
  | _ => none

/-- HOL `semantics_def`'s forbidden-result predicate: `False` for
`SOME TimeOut`/`SOME (FinalFFI _)`/`SOME (Return _)`, `True` otherwise. -/
def crepForbiddenResult {width : Nat} [NeZero width] :
    Option (CrepResultHOLExact width) → Prop
  | some .timeOut => False
  | some (.finalFfi _) => False
  | some (.return _) => False
  | _ => True

/-- `∃k.` the clock-`k` entry evaluation yields a forbidden result. -/
def crepHasForbiddenRun {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (start : MlString)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) : Prop :=
  ∃ clock, crepForbiddenResult (crepEvaluateClock state start memDec shMemDec clock).1

/-- `∃k t r outcome.` the clock-`k` entry evaluation yields a successful
`Return`/`FinalFFI` observation. -/
def crepHasSuccessfulRun {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (start : MlString)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) : Prop :=
  ∃ (clock : Nat) (result : Option (CrepResultHOLExact width))
    (final : CrepSemHOLState width σ),
    crepEvaluateClock state start memDec shMemDec clock = (result, final) ∧
      (crepResultOutcome result).isSome = true

/-- HOL `semantics_def`'s `some res` witness selection: pick a successful run
and return `Terminate outcome (event list)`. -/
noncomputable def crepChooseTermination {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (start : MlString)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (witness : crepHasSuccessfulRun state start memDec shMemDec) : CrepBehaviour :=
  let clock := Classical.choose witness
  let hrest := Classical.choose_spec witness
  let hrest2 := Classical.choose_spec hrest
  let hsome := (Classical.choose_spec hrest2).2
  .terminate (Classical.choose (Option.isSome_iff_exists.mp hsome))
    (crepResultEvents (crepEvaluateClock state start memDec shMemDec clock))

/-- HOL `semantics_def` with an explicit divergence LUB (the LUB is
`build_lprefix_lub (IMAGE (fromList ∘ SND ∘ evaluate) UNIV)` in HOL). -/
noncomputable def crepSemanticsWithLub {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (start : MlString)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (divergenceLub : PanLprefixLub
      (fun clock => crepResultEvents (crepEvaluateClock state start memDec shMemDec clock))) :
    CrepBehaviour := by
  classical
  exact if forbidden : crepHasForbiddenRun state start memDec shMemDec then
    .fail
  else if successful : crepHasSuccessfulRun state start memDec shMemDec then
    crepChooseTermination state start memDec shMemDec successful
  else
    .diverge _ divergenceLub

/-! ## Clock-indexed event traces form a lprefix chain (bead flapjack-pxn.18.4.8.2.6)

Given the HOL-shaped add-clock FFI-event prefix property (the
`crepPropsScript.sml:1020 evaluate_add_clock_io_events_mono` analogue), the
clock-indexed trace family of `crepSemantics` is a `panLprefixChain`.  This
packages the chain obligation so that `crepSemantics` no longer needs it as an
independent assumption.  Flapjack-specific infrastructure; no `@[hol]` tag. -/

/-- The clock-indexed FFI event traces of the exact crepSem entry evaluation
form a pairwise prefix chain, given the add-clock event-prefix property. -/
theorem crepEvaluateClock_ioEvents_lprefixChain_of_addClock_prefix
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (start : MlString)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (hmono : ∀ clock extra : Nat,
      crepResultEvents (crepEvaluateClock state start memDec shMemDec clock) <+:
      crepResultEvents (crepEvaluateClock state start memDec shMemDec (clock + extra))) :
    panLprefixChain (fun clock =>
      crepResultEvents (crepEvaluateClock state start memDec shMemDec clock)) := by
  intro left right
  rcases Nat.le_total left right with hle | hle
  · left
    have hprefix := hmono left (right - left)
    rwa [Nat.add_sub_cancel' hle] at hprefix
  · right
    have hprefix := hmono right (left - right)
    rwa [Nat.add_sub_cancel' hle] at hprefix

/-- The clock-indexed FFI event traces of the exact crepSem entry evaluation
form a pairwise prefix chain, derived from the exact evaluator's add-clock
event-prefix property (`crepPropsScript.sml:1020`).  Flapjack-specific
infrastructure; no `@[hol]` tag. -/
theorem crepEvaluateClock_ioEvents_lprefixChain {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (start : MlString)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    panLprefixChain (fun clock =>
      crepResultEvents (crepEvaluateClock state start memDec shMemDec clock)) := by
  apply crepEvaluateClock_ioEvents_lprefixChain_of_addClock_prefix state start memDec shMemDec
  intro clock extra
  have hmono :
      (evalCrepSemHOLProgExact ({ state with clock := clock } : CrepSemHOLState width σ)
          (crepEntryProgram start)).2.ffi.ioEvents <+:
        (evalCrepSemHOLProgExact ({ state with clock := clock + extra } : CrepSemHOLState width σ)
          (crepEntryProgram start)).2.ffi.ioEvents := by
    simpa only [crepStateAddClock] using
      (evalCrepSemHOLProgExact_addClockCombined (crepEntryProgram start)
        ({ state with clock := clock } : CrepSemHOLState width σ) extra).1
  simp only [evalCrepSemHOLProgExact_eq_core] at hmono
  simpa only [crepEvaluateClock, crepResultEvents] using hmono

/-- HOL `crepSem$semantics_def` with the shared prefix-LUB construction.  The
clock-indexed event family's `lprefix_chain` obligation is discharged from the
exact evaluator's add-clock event-prefix property
(`crepEvaluateClock_ioEvents_lprefixChain`), so no caller-supplied chain
argument is needed. -/
noncomputable def crepSemantics {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (start : MlString)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    CrepBehaviour :=
  crepSemanticsWithLub state start memDec shMemDec
    (buildPanLprefixLub _
      (crepEvaluateClock_ioEvents_lprefixChain state start memDec shMemDec))

/-- The caller-supplied-chain variant of `crepSemantics`, retained for callers
that already hold an independently proved `panLprefixChain`. -/
noncomputable def crepSemanticsWithChain {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (start : MlString)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (divergenceChain : panLprefixChain
      (fun clock => crepResultEvents (crepEvaluateClock state start memDec shMemDec clock))) :
    CrepBehaviour :=
  crepSemanticsWithLub state start memDec shMemDec
    (buildPanLprefixLub _ divergenceChain)

/-- HOL `crepSem$semantics_def` total variant: the divergence LUB is built from
the chain derived from the add-clock event-prefix property, so the only
remaining obligation is that property itself. -/
noncomputable def crepSemanticsOfAddClockPrefix {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (start : MlString)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (hmono : ∀ clock extra : Nat,
      crepResultEvents (crepEvaluateClock state start memDec shMemDec clock) <+:
      crepResultEvents (crepEvaluateClock state start memDec shMemDec (clock + extra))) :
    CrepBehaviour :=
  crepSemanticsWithLub state start memDec shMemDec
    (buildPanLprefixLub _
      (crepEvaluateClock_ioEvents_lprefixChain_of_addClock_prefix state start memDec shMemDec hmono))

end Flapjack
