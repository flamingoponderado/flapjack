import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.CrepProps.EvaluateAddClockIoEventsMono
import Flapjack.Misc.LprefixLub
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

This module gives the exact observational semantics over the exact
finite-support state `CrepSemHOLState`.  The entry evaluation uses the
no-decider evaluator `evalCrepSemHOLProgExact`; divergence uses HOL's total
`HolLList.buildLprefixLub` directly, with no caller-supplied chain or LUB.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace CrepObservationalSemantics

/-- Same-module canonical finite-support witness required by the qualified
`semantics_def` port below.  It re-exports the reviewed `CrepSemHOLState`
roundtrip from the exact evaluator module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemShMemExact.holFmapAsFiniteSupportWitness

end CrepObservationalSemantics

/-- HOL `semantics_def`'s entry program `Call NONE start []`. -/
def crepEntryProgram {width : Nat} [NeZero width] (start : MlString) :
    CrepProgHOL width :=
  .call none start []

/-- Clock-indexed entry evaluation `evaluate (Call NONE start [], s with clock := k)`,
returning the exact `(result option, state)` pair of HOL `evaluate`. -/
noncomputable def crepEvaluateClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (start : MlString)
    (clock : Nat) : Option (CrepResultHOLExact width) × CrepSemHOLState width σ :=
  evalCrepSemHOLProgExact { state with clock := clock } (crepEntryProgram start)

/-- The FFI event list of a clock-indexed evaluation result, i.e.
`(SND (evaluate (prog, s with clock := k))).ffi.io_events`. -/
def crepResultEvents {width : Nat} [NeZero width] {σ : Type}
    (pair : Option (CrepResultHOLExact width) × CrepSemHOLState width σ) :
    List HolIoEvent :=
  pair.2.ffi.ioEvents

/-- HOL `semantics_def`'s successful-result outcome mapping:
`SOME (Return _) => Success`, `SOME (FinalFFI e) => FFI_outcome e`, else none. -/
def crepResultOutcome {width : Nat} [NeZero width] :
    Option (CrepResultHOLExact width) → Option HolOutcome
  | some (.return _) => some .success
  | some (.finalFfi event) => some (.ffiOutcome event)
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
    (state : CrepSemHOLState width σ) (start : MlString) : Prop :=
  ∃ clock, crepForbiddenResult (crepEvaluateClock state start clock).1

/-- `∃k t r outcome.` the clock-`k` entry evaluation yields a successful
`Return`/`FinalFFI` observation. -/
def crepHasSuccessfulRun {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (start : MlString) : Prop :=
  ∃ (clock : Nat) (result : Option (CrepResultHOLExact width))
    (final : CrepSemHOLState width σ),
    crepEvaluateClock state start clock = (result, final) ∧
      (crepResultOutcome result).isSome = true

/-- HOL `semantics_def`'s `some res` witness selection: pick a successful run
and return `Terminate outcome (event list)`. -/
noncomputable def crepChooseTermination {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (start : MlString)
    (witness : crepHasSuccessfulRun state start) : HolBehaviour :=
  let clock := Classical.choose witness
  let hrest := Classical.choose_spec witness
  let hrest2 := Classical.choose_spec hrest
  let hsome := (Classical.choose_spec hrest2).2
  .terminate (Classical.choose (Option.isSome_iff_exists.mp hsome))
    (crepResultEvents (crepEvaluateClock state start clock))

/-- Exact port of HOL `crepSem$semantics_def` (`crepSemScript.sml:448-471`).
The finite-support fields of `CrepSemHOLState` implement HOL's finite maps;
the positive-width bitvectors and FFI host type are the reviewed conventional
carriers. The result and divergence constructors are the shared HOL carriers
`HolBehaviour`/`HolOutcome`, and the divergence branch applies total HOL
`build_lprefix_lub` directly to the `IMAGE` family. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "semantics_def"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
noncomputable def crepSemantics {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (start : MlString) : HolBehaviour := by
  classical
  let prog : CrepProgHOL width := crepEntryProgram start
  exact if ∃ k, (match (evalCrepSemHOLProgExact { state with clock := k } prog).1 with
      | some .timeOut => False
      | some (.finalFfi _) => False
      | some (.return _) => False
      | _ => True) then
    .fail
  else
    match holOptionSome (fun res => ∃ k t r outcome,
        evalCrepSemHOLProgExact { state with clock := k } prog = (r, t) ∧
        (match r with
         | some (.finalFfi event) => outcome = HolOutcome.ffiOutcome event
         | some (.return _) => outcome = HolOutcome.success
         | _ => False) ∧
        res = HolBehaviour.terminate outcome t.ffi.ioEvents) with
    | some res => res
    | none => .diverge (HolLList.buildLprefixLub (fun l => ∃ k,
        l = HolLList.fromList
          (evalCrepSemHOLProgExact { state with clock := k } prog).2.ffi.ioEvents))

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
    (hmono : ∀ clock extra : Nat,
      crepResultEvents (crepEvaluateClock state start clock) <+:
      crepResultEvents (crepEvaluateClock state start (clock + extra))) :
    panLprefixChain (fun clock =>
      crepResultEvents (crepEvaluateClock state start clock)) := by
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
    (state : CrepSemHOLState width σ) (start : MlString) :
    panLprefixChain (fun clock =>
      crepResultEvents (crepEvaluateClock state start clock)) := by
  apply crepEvaluateClock_ioEvents_lprefixChain_of_addClock_prefix state start
  intro clock extra
  have hmono :
      (evalCrepSemHOLProgExact ({ state with clock := clock } : CrepSemHOLState width σ)
          (crepEntryProgram start)).2.ffi.ioEvents <+:
        (evalCrepSemHOLProgExact ({ state with clock := clock + extra } : CrepSemHOLState width σ)
          (crepEntryProgram start)).2.ffi.ioEvents := by
    simpa only [crepStateAddClock] using
      (evalCrepSemHOLProgExact_addClockCombined (crepEntryProgram start)
        ({ state with clock := clock } : CrepSemHOLState width σ) extra).1
  simpa only [crepEvaluateClock, crepResultEvents] using hmono

end Flapjack
