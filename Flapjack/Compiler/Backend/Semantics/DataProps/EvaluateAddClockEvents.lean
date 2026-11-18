module

public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateAddClock
public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceCall
public import Flapjack.Misc.ClockWeightInduction
public import Flapjack.HolRef

@[expose] public section

/-!
# Event prefixes under clock extension

Counterpart of `cakeml/compiler/backend/semantics/dataPropsScript.sml:2134`
`evaluate_add_clock_io_events_mono`.

Extending the starting clock by `extra` cannot remove I/O events: the run at the
original clock produces an event prefix of the run at the extended clock. The
induction runs over the lexicographic `(clock, weight)` measure; each
constructor's step is a private lemma below.

The private helpers have no separate HOL original: they are the constructor
cases and commutation facts of the single HOL `recInduct evaluate_ind` proof,
split out so the induction can be assembled program by program.
-/

namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.DataSem

/-- A run at the original clock has an event prefix of the run at the extended
    clock. -/
private def AddClockEventsAt {C F : Type} (program : DataLang.Prog) (state : State C F) : Prop :=
  ∀ extra : Nat, (evaluate program state).2.ffi.ioEvents <+:
    (evaluate program (addClockState state extra)).2.ffi.ioEvents

/-- The events from a state to its run's final state. -/
private theorem evaluate_events_start {C F : Type} (program : DataLang.Prog)
    (state : State C F) :
    state.ffi.ioEvents <+: (evaluate program state).2.ffi.ioEvents := by
  cases runEq : evaluate program state with
  | mk res next =>
    have mono := evaluate_events_of_result program state res next runEq
    simpa using mono

/-- The run at the extended clock extends the starting events. -/
private theorem addClockEvents_big {C F : Type} (program : DataLang.Prog) (state : State C F)
    (extra : Nat) :
    state.ffi.ioEvents <+:
      (evaluate program (addClockState state extra)).2.ffi.ioEvents := by
  cases runEq : evaluate program (addClockState state extra) with
  | mk res next =>
    have mono := evaluate_events_of_result program (addClockState state extra) res next runEq
    simpa using mono

/-- If the small run's final FFI state is the starting one, the extended run's
    monotonicity suffices. -/
private theorem addClockEvents_viaStart {C F : Type} (program : DataLang.Prog)
    (state : State C F) (extra : Nat)
    (sameFfi : (evaluate program state).2.ffi = state.ffi) :
    (evaluate program state).2.ffi.ioEvents <+:
      (evaluate program (addClockState state extra)).2.ffi.ioEvents := by
  rw [sameFfi]
  exact addClockEvents_big program state extra

/-- A run that does not time out has exactly the extended run's events. -/
private theorem addClockEvents_of_not_timeout {C F : Type} (program : DataLang.Prog)
    (state : State C F) (extra : Nat)
    (res : Option (Result (List DataSem.Value) DataSem.Value)) (next : State C F)
    (run : evaluate program state = (res, next))
    (notTimeout : res ≠ some (.err (.abort .timeoutError))) :
    (evaluate program state).2.ffi.ioEvents <+:
      (evaluate program (addClockState state extra)).2.ffi.ioEvents := by
  have swap := evaluate_add_clock program state res next ⟨run, notTimeout⟩ extra
  rw [run, swap]
  exact List.prefix_refl _

/-- A primitive error is unchanged by a clock extension. -/
private theorem doApp_addClockState_err {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (ck : Nat)
    (error : ErrorResult DataSem.Value) (run : doApp op values state = .err error) :
    doApp op values (addClockState state ck) = .err error := by
  rw [doApp_addClockState, run]
  simp only [mapResult, mapErrorResult_id]

/-- A successful primitive result shifts with the clock extension. -/
private theorem doApp_addClockState_val {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (ck : Nat)
    (value : DataSem.Value) (next : State C F)
    (run : doApp op values state = .val (value, next)) :
    doApp op values (addClockState state ck) = .val (value, addClockState next ck) := by
  rw [doApp_addClockState, run]
  simp only [mapResult]

/-- A stopped program is unchanged by a clock extension. -/
private theorem addClockEvents_skip {C F : Type} (state : State C F) :
    AddClockEventsAt .skip state := by
  intro extra
  simp only [evaluate]
  exact List.prefix_refl _

/-- A move is unchanged by a clock extension. -/
private theorem addClockEvents_move {C F : Type} (dest src : Nat) (state : State C F) :
    AddClockEventsAt (.move dest src) state := by
  intro extra
  simp only [evaluate]
  cases read : getVar src state.locals with
  | none => simp [typeError]
  | some value => simp [setVar]

/-- An assignment is unchanged by a clock extension. -/
private theorem addClockEvents_assign {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (names : List Nat) (live : Option NumSet) (state : State C F) :
    AddClockEventsAt (.assign dest op names live) state := by
  intro extra
  simp only [evaluate]
  by_cases invalid : (DataLang.opRequiresNames op == live.isNone) = true
  · simp [invalid, typeError]
  · simp only [invalid] at ⊢
    cases read : getVars names state.locals with
    | none => simp [typeError]
    | some values =>
      cases cut : cutStateOpt live state with
      | none =>
        rw [cutStateOpt_addClockState live state extra, cut, Option.map_none] at ⊢
        simp [typeError]
      | some prepared =>
        rw [cutStateOpt_addClockState live state extra, cut, Option.map_some] at ⊢
        simp only []
        cases app : doApp op values prepared with
        | err error =>
          have shifted := doApp_addClockState_err op values prepared extra error app
          rw [shifted] at ⊢
          simp [flushState, installSfs]
        | val pair =>
          obtain ⟨value, last⟩ := pair
          have shifted := doApp_addClockState_val op values prepared extra value last app
          rw [shifted] at ⊢
          simp [installSfs, setVar]

/-- A tick either times out or decrements the clock on both sides. -/
private theorem addClockEvents_tick {C F : Type} (state : State C F) :
    AddClockEventsAt .tick state := by
  intro extra
  simp only [evaluate]
  by_cases zero : state.clock = 0
  · rw [if_pos zero]
    by_cases extraZero : extra = 0
    · have shiftZero : state.clock + extra = 0 := by omega
      rw [if_pos shiftZero]
      simp only [timeoutError, flushState]
      exact List.prefix_refl _
    · have shiftPos : ¬ state.clock + extra = 0 := by omega
      rw [if_neg shiftPos]
      simp only [timeoutError, flushState, decClock]
      exact List.prefix_refl _
  · rw [if_neg zero]
    have shiftPos : ¬ state.clock + extra = 0 := by omega
    rw [if_neg shiftPos]
    simp only [decClock]
    exact List.prefix_refl _

/-- Reserving space is unchanged by a clock extension. -/
private theorem addClockEvents_makeSpace {C F : Type} (amount : Nat) (names : NumSet)
    (state : State C F) : AddClockEventsAt (.makeSpace amount names) state := by
  intro extra
  simp only [evaluate]
  cases cut : cutEnv names state.locals with
  | none => simp [typeError]
  | some env =>
    simp only []
    have comm : { addClockState state extra with locals := env } =
        addClockState { state with locals := env } extra := rfl
    rw [comm, addSpace_addClockState]
    exact List.prefix_refl _

/-- Raising an exception is unchanged by a clock extension. -/
private theorem addClockEvents_raise {C F : Type} (name : Nat) (state : State C F) :
    AddClockEventsAt (.raise name) state := by
  intro extra
  simp only [evaluate]
  cases read : getVar name state.locals with
  | none => simp [typeError]
  | some value =>
    cases jump : jumpExc state with
    | none =>
      rw [jumpExc_addClockState, jump, Option.map_none] at ⊢
      simp [typeError]
    | some jumped =>
      simp only [jumpExc_addClockState, jump, Option.map_some]
      exact List.prefix_refl _

/-- Returning values is unchanged by a clock extension. -/
private theorem addClockEvents_return {C F : Type} (names : List Nat) (state : State C F) :
    AddClockEventsAt (.return names) state := by
  intro extra
  simp only [evaluate]
  cases read : getVars names state.locals with
  | none => simp [typeError]
  | some values =>
    simp only []
    rw [flushState_addClockState]
    exact List.prefix_refl _

/-- A conditional follows the branch its guard selects. -/
private theorem addClockEvents_if {C F : Type} (name : Nat) (yes no : DataLang.Prog)
    (state : State C F) (yesIH : AddClockEventsAt yes state) (noIH : AddClockEventsAt no state) :
    AddClockEventsAt (.ifThenElse name yes no) state := by
  intro extra
  simp only [evaluate]
  cases read : getVar name state.locals with
  | none => simp [typeError]
  | some value =>
    simp only []
    by_cases trueBranch : isBool true value = true
    · simp [trueBranch]
      exact yesIH extra
    · simp only [trueBranch] at ⊢
      by_cases falseBranch : isBool false value = true
      · simp [falseBranch]
        exact noIH extra
      · simp [falseBranch, typeError]

/-- A sequence follows its two programs at the clamped intermediate state. -/
private theorem addClockEvents_seq {C F : Type} (first second : DataLang.Prog)
    (state : State C F)
    (firstIH : AddClockEventsAt first state)
    (secondIH : ∀ mid : State C F, mid.clock ≤ state.clock → AddClockEventsAt second mid) :
    AddClockEventsAt (.seq first second) state := by
  intro extra
  simp only [evaluate]
  cases run1 : evaluate first state with
  | mk res1 next1 =>
    have h1 := firstIH extra
    rw [run1] at h1
    cases res1 with
    | none =>
      have swap1 := evaluate_add_clock first state none next1 ⟨run1, by simp⟩ extra
      rw [swap1]
      rw [fixClock_addClockState state none next1 extra]
      simp only [fixClock]
      let mid := (fixClock state
        ((none : Option (Result (List DataSem.Value) DataSem.Value)), next1)).2
      exact secondIH mid (by
        simp only [mid, fixClock]
        exact Nat.min_le_left _ _) extra
    | some result =>
      by_cases timeout : result = .err (.abort .timeoutError)
      · cases run1' : evaluate first (addClockState state extra) with
        | mk res1' next1' =>
          rw [run1'] at h1
          simp only [fixClock]
          cases res1' with
          | none =>
            refine h1.trans ?_
            exact evaluate_events_start second
              (fixClock (addClockState state extra) (none, next1')).2
          | some r =>
            exact h1
      · have swap1 := evaluate_add_clock first state (some result) next1
          ⟨run1, by simpa using timeout⟩ extra
        rw [swap1]
        simp only [fixClock]
        exact List.prefix_refl _

/-- The result dispatch of a direct force run has the run's own events. -/
private theorem forceDispatchEvents {C F : Type} (run : EvalResult C F) :
    (match run.1 with
      | none => typeError run.2
      | some value => (some value, run.2)).2.ffi.ioEvents =
      run.2.ffi.ioEvents := by
  cases run with
  | mk res next =>
    cases res with
    | none => simp [typeError]
    | some value => rfl

/-- The result dispatch of a returning force run has the run's own events. -/
private theorem forceRetDispatchEvents {C F : Type} (dest : Nat) (run : EvalResult C F) :
    (match run.1 with
      | some (.val [value]) =>
        match popEnv run.2 with
        | none => typeError run.2
        | some popped => (none, setVar dest value popped)
      | some (.val _) | none => typeError run.2
      | some (.err error) => (some (.err error), run.2)).2.ffi.ioEvents =
      run.2.ffi.ioEvents := by
  cases run with
  | mk res next =>
    cases res with
    | none => simp [typeError]
    | some result =>
      cases result with
      | err error => rfl
      | val values =>
        cases values with
        | nil => simp [typeError]
        | cons value rest =>
          cases rest with
          | nil =>
            cases stackEq : next.stack with
            | nil => simp [popEnv, stackEq, typeError]
            | cons frame frames =>
              cases frame with
              | env size envSpt => simp [popEnv, stackEq, setVar]
              | exc size envSpt handler => simp [popEnv, stackEq, setVar]
          | cons _ _ => simp [typeError]

set_option linter.unusedSimpArgs false in
/-- A force follows its thunk: the evaluated, direct, and body branches each
    extend the starting events. -/
private theorem addClockEvents_force {C F : Type} (ret : Option (Nat × NumSet))
    (label src : Nat) (state : State C F)
    (bodyIH : ∀ body : DataLang.Prog, ∀ next : State C F, next.clock < state.clock →
      AddClockEventsAt body next) :
    AddClockEventsAt (.force ret label src) state := by
  intro extra
  simp only [evaluate]
  cases read : getVar src state.locals with
  | none => simp [typeError]
  | some thunk =>
    simp only [read]
    generalize destEq : destThunk thunk state.refs = dest at ⊢
    cases dest with
    | badRef =>
      simp only []
      simp [typeError]
    | notThunk =>
      simp only []
      simp [typeError]
    | isThunk mode thunkValue =>
      cases mode with
      | evaluated =>
        simp only []
        cases ret with
        | none =>
          simp only []
          rw [flushState_addClockState]
          exact List.prefix_refl _
        | some retPair =>
          obtain ⟨dest', names⟩ := retPair
          simp only []
          cases cut : cutEnv names state.locals with
          | none => simp [typeError]
          | some env =>
            simp only []
            have comm : { addClockState state extra with locals := env } =
                addClockState { state with locals := env } extra := rfl
            rw [comm, setVar_addClockState]
            exact List.prefix_refl _
      | notEvaluated =>
        simp only []
        generalize foundEq : findCode (some label) [thunk, thunkValue] state.code
            state.stackFrameSizes = found at ⊢
        cases found with
        | none =>
          simp only []
          simp [typeError]
        | some entry =>
          obtain ⟨args, body, size⟩ := entry
          simp only []
          cases ret with
          | none =>
            simp only []
            by_cases zero : state.clock = 0
            · rw [if_pos zero]
              by_cases extraZero : extra = 0
              · have shiftZero : state.clock + extra = 0 := by omega
                rw [if_pos shiftZero]
                simp only [timeoutError]
                exact List.prefix_refl _
              · have shiftPos : ¬ state.clock + extra = 0 := by omega
                rw [if_neg shiftPos]
                simp only [timeoutError]
                have ffiEq : (callEnv args size
                    (decClock (addClockState state extra))).ffi = state.ffi := by
                  simp [callEnv, decClock]
                have start := evaluate_events_start body
                  (callEnv args size (decClock (addClockState state extra)))
                rw [ffiEq] at start
                generalize runEq : evaluate body
                  (callEnv args size (decClock (addClockState state extra))) = run at ⊢
                cases run with
                | mk res next =>
                  rw [runEq] at start
                  cases res with
                  | none => simpa [typeError] using start
                  | some value => simpa using start
            · rw [if_neg zero]
              have shiftPos : ¬ state.clock + extra = 0 := by omega
              rw [if_neg shiftPos]
              rw [decClock_addClockState state extra zero, callEnv_addClockState]
              have h := bodyIH body (callEnv args size (decClock state)) (by
                simp only [callEnv, decClock]
                omega) extra
              generalize runEq : evaluate body (callEnv args size (decClock state)) = run at ⊢
              generalize shiftEq : evaluate body
                  (addClockState (callEnv args size (decClock state)) extra) = shiftRun at ⊢
              rw [runEq, shiftEq] at h
              cases run with
              | mk res next =>
                cases shiftRun with
                | mk res' next' =>
                  cases res <;> cases res' <;> simpa [typeError] using h
          | some retPair =>
            obtain ⟨dest', names⟩ := retPair
            simp only []
            cases cut : cutEnv names state.locals with
            | none => simp [typeError]
            | some env =>
              simp only []
              by_cases zero : state.clock = 0
              · rw [if_pos zero]
                by_cases extraZero : extra = 0
                · have shiftZero : state.clock + extra = 0 := by omega
                  rw [if_pos shiftZero]
                  simp only [timeoutError]
                  exact List.prefix_refl _
                · have shiftPos : ¬ state.clock + extra = 0 := by omega
                  rw [if_neg shiftPos]
                  simp only [timeoutError]
                  have ffiEq : (callEnv args size
                      (pushEnv env false (decClock (addClockState state extra)))).ffi =
                      state.ffi := by
                    simp [callEnv, pushEnv, decClock]
                  have start := evaluate_events_start body
                    (callEnv args size (pushEnv env false (decClock (addClockState state extra))))
                  rw [ffiEq] at start
                  generalize runEq : evaluate body (callEnv args size (pushEnv env false
                    (decClock (addClockState state extra)))) = run at ⊢
                  have rightEq := forceRetDispatchEvents dest' (fixClock
                    (callEnv args size (pushEnv env false (decClock (addClockState state extra))))
                    run)
                  rw [runEq] at start
                  simp only [fixClock] at rightEq
                  simp only [callEnv, pushEnv, decClock] at rightEq ⊢
                  exact rightEq.symm ▸ start
              · rw [if_neg zero]
                have shiftPos : ¬ state.clock + extra = 0 := by omega
                rw [if_neg shiftPos]
                rw [decClock_addClockState state extra zero, pushEnv_addClockState,
                  callEnv_addClockState]
                have h := bodyIH body
                  (callEnv args size (pushEnv env false (decClock state))) (by
                  simp only [callEnv, pushEnv, decClock]
                  omega) extra
                generalize runEq : evaluate body
                  (callEnv args size (pushEnv env false (decClock state))) = run at ⊢
                generalize shiftEq : evaluate body (addClockState (callEnv args size
                  (pushEnv env false (decClock state))) extra) = shiftRun at ⊢
                rw [runEq, shiftEq] at h
                have leftEq := forceRetDispatchEvents dest' (fixClock
                  (callEnv args size (pushEnv env false (decClock state))) run)
                have rightEq := forceRetDispatchEvents dest' (fixClock
                  (addClockState (callEnv args size (pushEnv env false (decClock state))) extra)
                  shiftRun)
                simp only [fixClock] at leftEq rightEq ⊢
                exact leftEq.symm ▸ rightEq.symm ▸ h

/-- The result dispatch of a returning call extends the run's events.
    Flapjack infrastructure for `evaluate_add_clock_io_events_mono`; no separate
    HOL original. The handler arm destructures `some (name, body)` exactly as
    `evaluate` does: a `some entry` binder with `entry.1`/`entry.2` projections
    compiles to a different `Option.casesOn` term, so the statement would not be
    definitionally equal to the evaluator's own dispatch. -/
private theorem callRetDispatchEvents_ge {C F : Type} (returns : List Nat)
    (handler : Option (Nat × DataLang.Prog)) (run : EvalResult C F) :
    run.2.ffi.ioEvents <+:
      (match run.1 with
        | some (.val values) =>
          if values.length = returns.length then
            match popEnv run.2 with
            | none => typeError run.2
            | some popped => (none, setVars returns values popped)
          else typeError run.2
        | some (.err (.raise value)) =>
          match handler with
          | none => (some (.err (.raise value)), run.2)
          | some (name, body) => evaluate body (setVar name value run.2)
        | none => typeError run.2
        | some (.err error) => (some (.err error), run.2)).2.ffi.ioEvents := by
  cases run with
  | mk res next =>
    cases res with
    | none => simp [typeError]
    | some result =>
      cases result with
      | val values =>
        simp only []
        by_cases sameLength : values.length = returns.length
        · rw [if_pos sameLength]
          cases stackEq : next.stack with
          | nil => simp [popEnv, stackEq, typeError]
          | cons frame frames =>
            cases frame with
            | env frameSize envSpt => simp [popEnv, stackEq, setVars]
            | exc frameSize envSpt frameHandler => simp [popEnv, stackEq, setVars]
        · rw [if_neg sameLength]
          simp [typeError]
      | err error =>
        cases error with
        | abort reason => simp
        | raise value =>
          cases handler with
          | none => simp
          | some pair =>
            obtain ⟨name, body⟩ := pair
            simpa [setVar] using evaluate_events_start body (setVar name value next)

end Flapjack.Compiler.Backend.DataProps
