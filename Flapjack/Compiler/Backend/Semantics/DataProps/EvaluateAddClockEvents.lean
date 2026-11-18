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

end Flapjack.Compiler.Backend.DataProps
