import Flapjack.Pancake.Semantics.PanSem.PanObservationalSemantics

/-!
# Source parity for the clock-indexed `panSem$semantics_def` observations

The source reference is `cakeml/pancake/semantics/panSemScript.sml:785-809`
(`semantics_def`).  It repeatedly evaluates `Call NONE start []` at the
clock-indexed states `s with clock := k` and classifies the first components of
the resulting `evaluate` pairs into: forbidden (`Fail`), successful
`Return`/`FinalFFI` (`Terminate`), or neither (`Diverge` over the
`build_lprefix_lub` of the event prefixes).

The direct original-HOL EVAL rows for the `evaluate` observations this consumes
are:
* timeout: `tick_zero_result=SOME TimeOut` in `pan_sem_tick_e2e_probe.out`;
* return: `return_41=SOME (Return (ValWord 41w))` in `pan_sem_e2e_probe.out`;
* FFI event: `ffi_foo_event=[IO_event (ExtCall «foo») ...]` in
  `pan_sem_ffi_e2e_probe.out`;
* forbidden results: `ret_eval_fail_result=SOME Error` and
  `raise_ok_result=SOME (Exception «E» (ValWord 7w))` in
  `pan_sem_return_raise_error_probe.out`.

These checks exercise the exact observation adapters `panExactForbiddenResult`,
`panExactResultOutcome`, `panExactResultEvents`, and the branch selection of
`panSemanticsExactTotal` on the classification rows above.  No `@[hol]` tag is
attached to the semantics definitions (see the module note in
`Flapjack.Pancake.Semantics.PanSem.PanObservationalSemantics`).
-/

namespace Flapjack.Test.PanSemanticsObservationsParity

open Flapjack

/-- HOL `semantics_def` treats `SOME TimeOut` as NOT forbidden
(`tick_zero_result=SOME TimeOut`). -/
example : ¬ panExactForbiddenResult
    (some (PanSemResultExact.timeOut (width := 64))) := by
  simp [panExactForbiddenResult]

/-- HOL `semantics_def` treats `SOME (Return _)` as NOT forbidden
(`return_41=SOME (Return (ValWord 41w))`). -/
example (value : ValueHOL 64) : ¬ panExactForbiddenResult
    (some (PanSemResultExact.returned (width := 64) value)) := by
  simp [panExactForbiddenResult]

/-- HOL `semantics_def` treats `SOME (FinalFFI _)` as NOT forbidden
(`ffi_foo_event`). -/
example (event : HolFinalEvent) : ¬ panExactForbiddenResult
    (some (PanSemResultExact.finalFfi (width := 64) event)) := by
  simp [panExactForbiddenResult]

/-- HOL `semantics_def` treats `SOME Error` as forbidden
(`ret_eval_fail_result=SOME Error`). -/
example : panExactForbiddenResult
    (some (PanSemResultExact.error (width := 64))) := by
  trivial

/-- HOL `semantics_def` treats `SOME (Exception _ _)` as forbidden
(`raise_ok_result=SOME (Exception «E» (ValWord 7w))`). -/
example (eid : Flapjack.Pancake.PanLang.MlS) (value : ValueHOL 64) :
    panExactForbiddenResult
      (some (PanSemResultExact.exception (width := 64) eid value)) := by
  trivial

/-- HOL `semantics_def` treats the unassembled `NONE` result as forbidden. -/
example : panExactForbiddenResult (none : Option (PanSemResultExact 64)) := by
  trivial

/-- A `Return` yields the `Success` outcome. -/
example (value : ValueHOL 64) :
    panExactResultOutcome (some (PanSemResultExact.returned (width := 64) value)) =
      some .success := rfl

/-- A `FinalFFI e` yields the `FFI_outcome` of its final event. -/
example (event : HolFinalEvent) :
    panExactResultOutcome (some (PanSemResultExact.finalFfi (width := 64) event)) =
      some (.ffi event.outcome) := rfl

/-- `TimeOut` has no successful outcome, matching the `tick_zero` row. -/
example : panExactResultOutcome (some (PanSemResultExact.timeOut (width := 64))) =
    (none : Option PanSemExactOutcome) := rfl

/-- A forbidden run makes `semantics_def` return `Fail`, with no extra
hypothesis beyond the evaluator-derived divergence chain. -/
theorem forbidden_returns_fail {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (start : Flapjack.Pancake.PanLang.MlS)
    (hforbidden : panExactHasForbiddenRun context start) :
    panSemanticsExactTotal context start = .fail := by
  unfold panSemanticsExactTotal panSemanticsExact panSemanticsExactWithLub
  simp only [dif_pos hforbidden]

/-- A successful `Return`/`FinalFFI` witness with no forbidden run terminates
with the chosen outcome and the clock-indexed event list columns. -/
theorem successful_returns_terminate {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (start : Flapjack.Pancake.PanLang.MlS)
    (hforbidden : ¬ panExactHasForbiddenRun context start)
    (hsuccessful : panExactHasSuccessfulRun context start) :
    panSemanticsExactTotal context start =
      panExactChooseTermination context start hsuccessful := by
  unfold panSemanticsExactTotal panSemanticsExact panSemanticsExactWithLub
  simp only [dif_neg hforbidden, dif_pos hsuccessful]

/-- With neither a forbidden nor a successful run the semantics diverges over
the evaluator-derived LUB of the clock-indexed event family. -/
theorem no_run_diverges {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (start : Flapjack.Pancake.PanLang.MlS)
    (hforbidden : ¬ panExactHasForbiddenRun context start)
    (hsuccessful : ¬ panExactHasSuccessfulRun context start) :
    panSemanticsExactTotal context start =
      .diverge (fun clock => panExactResultEvents (panEvaluateClock context start clock))
        (buildPanLprefixLub _
          (panEvaluateClock_ioEvents_lprefixChain context start)) := by
  unfold panSemanticsExactTotal panSemanticsExact panSemanticsExactWithLub
  simp only [dif_neg hforbidden, dif_neg hsuccessful]

def runChecks : IO Bool := do
  IO.println "PASS panSem semantics clock-indexed observation classification"
  IO.println "PASS panSem semantics branch selection over exact evaluator"
  pure true

end Flapjack.Test.PanSemanticsObservationsParity
