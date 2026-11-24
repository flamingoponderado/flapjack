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

set_option linter.unusedSimpArgs false in
/-- A call runs the callee body and, on a raised exception, the handler.
    Flapjack infrastructure for `evaluate_add_clock_io_events_mono`; no separate
    HOL original. -/
private theorem addClockEvents_call {C F : Type} (ret : Option (List Nat × NumSet))
    (dest : Option Nat) (names : List Nat) (handler : Option (Nat × DataLang.Prog))
    (state : State C F)
    (bodyIH : ∀ body : DataLang.Prog, ∀ next : State C F, next.clock < state.clock →
      AddClockEventsAt body next) :
    AddClockEventsAt (.call ret dest names handler) state := by
  intro extra
  simp only [evaluate]
  cases read : DataSem.getVars names state.locals with
  | none =>
    simp [typeError, addClockState]
  | some values =>
    simp only [read]
    generalize foundEq : DataSem.findCode dest values state.code state.stackFrameSizes = found at ⊢
    cases found with
    | none =>
      simp [typeError, addClockState]
    | some entry =>
      obtain ⟨args, body, size⟩ := entry
      simp only []
      cases ret with
      | none =>
        simp only []
        by_cases someHandler : handler.isSome = true
        · simp [someHandler, typeError, addClockState]
        · simp only [someHandler, Bool.false_eq_true, if_false] at ⊢
          by_cases zero : state.clock = 0
          · by_cases extraZero : extra = 0
            · have shiftZero : state.clock + extra = 0 := by omega
              rw [if_pos zero, if_pos shiftZero]
              simp [someHandler, timeoutError, flushState, addClockState]
            · have shiftPos : ¬ state.clock + extra = 0 := by omega
              rw [if_pos zero, if_neg shiftPos]
              simp only [timeoutError, flushState]
              have ffiEq : (DataSem.callEnv args size
                  (decClock (addClockState state extra))).ffi = state.ffi := by
                simp [DataSem.callEnv, decClock]
              have start := evaluate_events_start body
                (DataSem.callEnv args size (decClock (addClockState state extra)))
              rw [ffiEq] at start
              generalize runEq : evaluate body
                  (DataSem.callEnv args size (decClock (addClockState state extra))) = run at ⊢
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
            have h := bodyIH body (DataSem.callEnv args size (decClock state)) (by
              simp only [DataSem.callEnv, decClock]
              omega) extra
            generalize runEq : evaluate body
                (DataSem.callEnv args size (decClock state)) = run at ⊢
            generalize shiftEq : evaluate body
                (addClockState (DataSem.callEnv args size (decClock state)) extra) = shiftRun at ⊢
            rw [runEq, shiftEq] at h
            cases run with
            | mk res next =>
              cases shiftRun with
              | mk res' next' =>
                cases res <;> cases res' <;> simpa [typeError, someHandler] using h
      | some retPair =>
        obtain ⟨returns, live⟩ := retPair
        simp only []
        by_cases nodup : (!returns.Nodup) = true
        · simp [nodup, typeError, addClockState]
        · simp only [nodup, Bool.false_eq_true, if_false] at ⊢
          cases cut : DataSem.cutEnv live state.locals with
          | none =>
            simp [nodup, typeError, addClockState]
          | some env =>
            simp only []
            by_cases zero : state.clock = 0
            · rw [if_pos zero]
              by_cases extraZero : extra = 0
              · have shiftZero : state.clock + extra = 0 := by omega
                rw [if_pos shiftZero]
                simp [nodup, timeoutError, DataSem.callEnv, DataSem.pushEnv, decClock,
                  addClockState]
              · have shiftPos : ¬ state.clock + extra = 0 := by omega
                rw [if_neg shiftPos]
                simp only [timeoutError]
                have ffiEq : (DataSem.callEnv args size
                    (DataSem.pushEnv env handler.isSome
                      (decClock (addClockState state extra)))).ffi =
                    (DataSem.callEnv args size
                      (DataSem.pushEnv env handler.isSome (decClock state))).ffi := by
                  simp [DataSem.callEnv, DataSem.pushEnv, decClock, addClockState]
                have start := evaluate_events_start body
                  (DataSem.callEnv args size
                    (DataSem.pushEnv env handler.isSome (decClock (addClockState state extra))))
                rw [ffiEq] at start
                generalize runEq : evaluate body
                    (DataSem.callEnv args size
                      (DataSem.pushEnv env handler.isSome
                        (decClock (addClockState state extra)))) = run at ⊢
                cases run with
                | mk res next =>
                  rw [runEq] at start
                  have geRight := callRetDispatchEvents_ge returns handler (fixClock
                    (DataSem.callEnv args size
                      (DataSem.pushEnv env handler.isSome
                        (decClock (addClockState state extra)))) (res, next))
                  simp only [fixClock] at geRight ⊢
                  refine List.IsPrefix.trans ?_ geRight
                  exact start
            · rw [if_neg zero]
              have shiftPos : ¬ state.clock + extra = 0 := by omega
              rw [if_neg shiftPos]
              simp only [decClock_addClockState state extra zero, pushEnv_addClockState,
                callEnv_addClockState] at ⊢
              have h := bodyIH body
                (DataSem.callEnv args size
                  (DataSem.pushEnv env handler.isSome (decClock state))) (by
                simp only [DataSem.callEnv, DataSem.pushEnv, decClock]
                omega) extra
              generalize runEq : evaluate body
                  (DataSem.callEnv args size
                    (DataSem.pushEnv env handler.isSome (decClock state))) = run at ⊢
              cases run with
              | mk res next =>
                rw [runEq] at h
                cases res with
                | none =>
                  cases shiftEq : evaluate body
                      (addClockState (DataSem.callEnv args size
                        (DataSem.pushEnv env handler.isSome (decClock state))) extra) with
                  | mk res' next' =>
                    rw [shiftEq] at h
                    have geRight := callRetDispatchEvents_ge returns handler (fixClock
                      (addClockState (DataSem.callEnv args size
                        (DataSem.pushEnv env handler.isSome (decClock state))) extra)
                      (res', next'))
                    simp only [fixClock, typeError] at geRight ⊢
                    refine List.IsPrefix.trans ?_ geRight
                    exact h
                | some result =>
                  cases result with
                  | val values =>
                    by_cases sameLength : values.length = returns.length
                    · cases shiftEq : evaluate body
                          (addClockState (DataSem.callEnv args size
                            (DataSem.pushEnv env handler.isSome (decClock state))) extra) with
                      | mk res' next' =>
                        rw [shiftEq] at h
                        simp only [fixClock] at ⊢
                        simp only [if_pos sameLength] at ⊢
                        have geRight := callRetDispatchEvents_ge returns handler (fixClock
                          (addClockState (DataSem.callEnv args size
                            (DataSem.pushEnv env handler.isSome (decClock state))) extra)
                          (res', next'))
                        simp only [fixClock] at geRight ⊢
                        cases stackEq : next.stack with
                        | nil =>
                          simp only [popEnv, stackEq, typeError] at ⊢
                          refine List.IsPrefix.trans ?_ geRight
                          exact h
                        | cons frame frames =>
                          cases frame with
                          | env frameSize envSpt =>
                            simp only [popEnv, stackEq, setVars] at ⊢
                            refine List.IsPrefix.trans ?_ geRight
                            exact h
                          | exc frameSize envSpt frameHandler =>
                            simp only [popEnv, stackEq, setVars] at ⊢
                            refine List.IsPrefix.trans ?_ geRight
                            exact h
                    · cases shiftEq : evaluate body
                          (addClockState (DataSem.callEnv args size
                            (DataSem.pushEnv env handler.isSome (decClock state))) extra) with
                      | mk res' next' =>
                        rw [shiftEq] at h
                        simp only [fixClock] at ⊢
                        simp only [if_neg sameLength] at ⊢
                        have geRight := callRetDispatchEvents_ge returns handler (fixClock
                          (addClockState (DataSem.callEnv args size
                            (DataSem.pushEnv env handler.isSome (decClock state))) extra)
                          (res', next'))
                        simp only [fixClock, typeError] at geRight ⊢
                        refine List.IsPrefix.trans ?_ geRight
                        exact h
                  | err error =>
                    cases error with
                    | abort reason =>
                      cases shiftEq : evaluate body
                          (addClockState (DataSem.callEnv args size
                            (DataSem.pushEnv env handler.isSome (decClock state))) extra) with
                      | mk res' next' =>
                        rw [shiftEq] at h
                        have geRight := callRetDispatchEvents_ge returns handler (fixClock
                          (addClockState (DataSem.callEnv args size
                            (DataSem.pushEnv env handler.isSome (decClock state))) extra)
                          (res', next'))
                        simp only [fixClock, typeError] at geRight ⊢
                        refine List.IsPrefix.trans ?_ geRight
                        exact h
                    | raise value =>
                      cases handlerEq : handler with
                      | none =>
                        rw [handlerEq] at h
                        simp only [Option.isSome_none, Bool.false_eq_true, if_false] at h ⊢
                        cases shiftEq : evaluate body
                            (addClockState (DataSem.callEnv args size
                              (DataSem.pushEnv env false (decClock state))) extra) with
                        | mk res' next' =>
                          rw [shiftEq] at h
                          have geRight := callRetDispatchEvents_ge returns none (fixClock
                            (addClockState (DataSem.callEnv args size
                              (DataSem.pushEnv env false (decClock state))) extra)
                            (res', next'))
                          simp only [fixClock] at geRight ⊢
                          refine List.IsPrefix.trans ?_ geRight
                          exact h
                      | some handlerPair =>
                        obtain ⟨handlerName, handlerBody⟩ := handlerPair
                        rw [handlerEq] at h runEq
                        have isSomeEq : (some (handlerName, handlerBody)).isSome = true := rfl
                        rw [isSomeEq] at h runEq ⊢
                        have bodySwap := evaluate_add_clock body
                          (DataSem.callEnv args size
                            (DataSem.pushEnv env true (decClock state)))
                          (some (.err (.raise value))) next ⟨runEq, by simp⟩ extra
                        rw [bodySwap] at ⊢
                        simp only [fixClock_addClockState, setVar_addClockState] at ⊢
                        let handlerState : State C F := DataSem.setVar handlerName value
                          (fixClock (DataSem.callEnv args size
                            (DataSem.pushEnv env true (decClock state)))
                            ((some (.err (.raise value)) : Option (Result (List DataSem.Value)
                              DataSem.Value)), next)).2
                        have handlerClock : handlerState.clock < state.clock := by
                          simp only [handlerState, DataSem.setVar, fixClock]
                          exact lt_of_le_of_lt (Nat.min_le_left _ _) (by
                            simp only [DataSem.callEnv, DataSem.pushEnv, decClock]
                            omega)
                        exact bodyIH handlerBody handlerState handlerClock extra

/-- Every program satisfies the event-prefix property, by the lexicographic
    `(clock, weight)` induction over the program. -/
private theorem addClockEvents_all {C F : Type} (program : DataLang.Prog) (state : State C F) :
    AddClockEventsAt program state := by
  refine clockWeightInduction (α := DataLang.Prog) (σ := State C F) (·.clock) sizeOf
    (motive := fun program state => AddClockEventsAt program state) ?_ program state
  intro program state exprIH smaller
  cases program with
  | skip => exact addClockEvents_skip state
  | move dest src => exact addClockEvents_move dest src state
  | assign dest op names live => exact addClockEvents_assign dest op names live state
  | tick => exact addClockEvents_tick state
  | makeSpace amount names => exact addClockEvents_makeSpace amount names state
  | raise name => exact addClockEvents_raise name state
  | «return» names => exact addClockEvents_return names state
  | seq first second =>
    apply addClockEvents_seq first second state
    · exact exprIH first state (by omega)
        (by
          simp only [DataLang.Prog.seq.sizeOf_spec]
          omega)
    · intro mid bound
      exact exprIH second mid bound
        (by
          simp only [DataLang.Prog.seq.sizeOf_spec]
          omega)
  | ifThenElse name yes no =>
    apply addClockEvents_if name yes no state
    · exact exprIH yes state (by omega)
        (by
          simp only [DataLang.Prog.ifThenElse.sizeOf_spec]
          omega)
    · exact exprIH no state (by omega)
        (by
          simp only [DataLang.Prog.ifThenElse.sizeOf_spec]
          omega)
  | force ret label src =>
    apply addClockEvents_force ret label src state
    intro body next clockLt
    exact smaller body next clockLt
  | call ret dest names handler =>
    apply addClockEvents_call ret dest names handler state
    intro body next clockLt
    exact smaller body next clockLt

/-- Extending the starting clock by `extra` cannot remove I/O events: the run at
    the original clock produces an event prefix of the run at the extended clock.
    Port of HOL `evaluate_add_clock_io_events_mono`. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_add_clock_io_events_mono"]
theorem evaluate_add_clock_io_events_mono {C F : Type} (exps : DataLang.Prog)
    (state : State C F) (extra : Nat) :
    (evaluate exps state).2.ffi.ioEvents <+:
      (evaluate exps { state with clock := state.clock + extra }).2.ffi.ioEvents :=
  addClockEvents_all exps state extra

end Flapjack.Compiler.Backend.DataProps
