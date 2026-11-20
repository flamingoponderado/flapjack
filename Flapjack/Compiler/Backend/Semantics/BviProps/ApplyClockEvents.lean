module

public import Flapjack.Compiler.Backend.Semantics.BviProps.ApplyClockShift
public import Flapjack.Compiler.Backend.Semantics.BviProps.ApplyEvents
public import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateClockShift
public import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateEvents
public import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateEventsClockFull
public import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateList
public import Flapjack.HolRef

@[expose] public section

/-!
# Clock and I/O-event monotonicity of HOL `bviProps`

Counterpart of `cakeml/compiler/backend/semantics/bviPropsScript.sml:514-645`:
`do_app_change_clock`, `do_app_change_clock_err`, `evaluate_add_clock`,
`do_app_io_events_mono`, `evaluate_io_events_mono` and
`evaluate_add_to_clock_io_events_mono`. Each keeps HOL's binder order, single
premise and conclusion shape; the underlying facts are the untagged BVI
dispatcher and evaluator lemmas in the neighbouring modules.
-/

namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

namespace ClockEventsCarrier
/-- Canonical BVI reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BviSem.BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end ClockEventsCarrier

/-- A successful primitive application commutes with replacing the clock. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_change_clock"
  (fmap_as_finite_support := [refs])]
theorem doApp_change_clock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F) (res : Value)
    (next : Flapjack.Compiler.Backend.BviSem.BviState C F) (ck : Nat)
    (run : doApp op args state = .val (res, next)) :
    doApp op args { state with clock := ck } = .val (res, { next with clock := ck }) := by
  rw [doApp_setClock, run]
  rfl

/-- A primitive error is unaffected by replacing the clock. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_change_clock_err"
  (fmap_as_finite_support := [refs])]
theorem doApp_change_clock_err {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (error : ErrorResult ExnOrRet) (ck : Nat)
    (run : doApp op args state = .err error) :
    doApp op args { state with clock := ck } = .err error := by
  rw [doApp_setClock, run]
  rfl

/-- Non-timeout evaluation is stable under an added clock allowance. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "evaluate_add_clock"
  (fmap_as_finite_support := [refs])]
theorem evaluateAddClock {C F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F) (result : BviResult)
    (next : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (run : evaluateTuple (expressions, env, state) = (result, next) ∧
      result ≠ .err (.abort .timeoutError)) :
    ∀ ck, evaluateTuple (expressions, env, incClock ck state) =
      (result, incClock ck next) := by
  intro ck
  obtain ⟨runEq, notTimeout⟩ := run
  exact evaluate_addClock expressions env state next result ck runEq notTimeout

/-- A successful primitive application extends the I/O-event trace. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_io_events_mono"
  (fmap_as_finite_support := [refs])]
theorem doApp_io_events_mono {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F) (value : Value)
    (next : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (run : doApp op args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents :=
  doApp_ioEvents_prefix op args state next value run

/-- Evaluation extends the I/O-event trace. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "evaluate_io_events_mono"
  (fmap_as_finite_support := [refs])]
theorem evaluate_io_events_mono {C F : Type} (expressions : List Bvi.Exp)
    (env : List Value) (state : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (result : BviResult) (next : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (run : evaluateTuple (expressions, env, state) = (result, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents := by
  have growth := evaluate_ioEvents_prefix expressions env state
  rw [evaluateTuple] at run
  rw [run] at growth
  exact growth

/-- Increasing the evaluation clock extends its I/O-event trace. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml"
  "evaluate_add_to_clock_io_events_mono"
  (fmap_as_finite_support := [refs])]
theorem evaluate_add_to_clock_io_events_mono {C F : Type} (expressions : List Bvi.Exp)
    (env : List Value) (state : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (extra : Nat) :
    (evaluate expressions env state).2.ffi.ioEvents <+:
      (evaluate expressions env (incClock extra state)).2.ffi.ioEvents := by
  have growth := evaluate_addClock_ioEvents_prefix expressions env state extra
  simpa [incClock] using growth

end Flapjack.Compiler.Backend.BviProps
