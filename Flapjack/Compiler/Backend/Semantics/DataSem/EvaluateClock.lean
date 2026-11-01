import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyClock

/-! Clock-bound building blocks for data-language evaluation. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- A successful local-environment cut preserves the clock. -/
theorem cutStateOpt_clock {C F : Type} (live : Option NumSet) (state next : State C F)
    (run : cutStateOpt live state = some next) : next.clock = state.clock :=
  (cutStateOpt_control live state next run).2.2.2.2

/-- A successful exception-stack jump preserves the clock. -/
theorem jumpExc_clock {C F : Type} (state next : State C F) (run : jumpExc state = some next) :
    next.clock = state.clock := by
  unfold jumpExc at run
  split at run
  · split at run <;> simp_all
    subst next
    rfl
  · simp at run

/-- Assignment evaluation never increases the clock, including installation
and primitive errors. This is infrastructure for the evaluator clock bound. -/
theorem evaluate_assign_clock {C F : Type} (dest : Nat) (op : ClosLang.Op) (names : List Nat)
    (live : Option NumSet) (state : State C F) :
    (evaluate (.assign dest op names live) state).2.clock ≤ state.clock := by
  by_cases invalid : (DataLang.opRequiresNames op == live.isNone) = true
  · simp [evaluate, invalid]
  · cases read : getVars names state.locals with
    | none => simp [evaluate, invalid, read]
    | some args =>
      cases cut : cutStateOpt live state with
      | none => simp [evaluate, invalid, read, cut]
      | some prepared =>
        have cutClock := cutStateOpt_clock live state prepared cut
        cases app : doApp op args prepared with
        | err error => simp [evaluate, invalid, read, cut, app, flushState, installSfs, cutClock]
        | val pair =>
          obtain ⟨value, applied⟩ := pair
          have appClock := doApp_clock op args prepared applied value app
          simp [evaluate, invalid, read, cut, app, setVar, installSfs, appClock, cutClock]

/-- Moves do not increase the clock. -/
theorem evaluate_move_clock {C F : Type} (dest src : Nat) (state : State C F) :
    (evaluate (.move dest src) state).2.clock ≤ state.clock := by
  simp only [evaluate]
  split <;> simp [setVar]

/-- Reserving space does not increase the clock. -/
theorem evaluate_makeSpace_clock {C F : Type} (amount : Nat) (names : NumSet) (state : State C F) :
    (evaluate (.makeSpace amount names) state).2.clock ≤ state.clock := by
  simp only [evaluate]
  split <;> simp [addSpace]

/-- Raising an exception does not increase the clock. -/
theorem evaluate_raise_clock {C F : Type} (name : Nat) (state : State C F) :
    (evaluate (.raise name) state).2.clock ≤ state.clock := by
  cases read : getVar name state.locals with
  | none => simp [evaluate, read]
  | some value =>
    cases jump : jumpExc state with
    | none => simp [evaluate, read, jump]
    | some next => simp [evaluate, read, jump, jumpExc_clock state next jump]

/-- Returning values does not increase the clock. -/
theorem evaluate_return_clock {C F : Type} (names : List Nat) (state : State C F) :
    (evaluate (.return names) state).2.clock ≤ state.clock := by
  simp only [evaluate]
  split <;> simp [flushState]

/-- A tick either decrements the clock or reports a timeout. -/
theorem evaluate_tick_clock {C F : Type} (state : State C F) :
    (evaluate .tick state).2.clock ≤ state.clock := by
  simp [evaluate, decClock]
  split <;> simp_all [flushState]

/-- A normally continuing sequence respects the clock bound when its second
program does so at every clamped intermediate state. -/
theorem evaluate_seq_clock_step {C F : Type} (first second : DataLang.Prog) (state : State C F)
    (secondClock : ∀ mid : State C F, mid.clock ≤ state.clock →
      (evaluate second mid).2.clock ≤ mid.clock) :
    (evaluate (.seq first second) state).2.clock ≤ state.clock := by
  have bound : (fixClock state (evaluate first state)).2.clock ≤ state.clock := by
    simp [fixClock, Nat.min_le_left]
  rw [evaluate]
  generalize firstRun : fixClock state (evaluate first state) = pair at *
  obtain ⟨result, mid⟩ := pair
  change mid.clock ≤ state.clock at bound
  cases result with
  | some value => exact bound
  | none => exact Nat.le_trans (secondClock mid bound) bound

/-- If both branches obey the clock bound, so does a conditional. -/
theorem evaluate_if_clock_step {C F : Type} (name : Nat) (yes no : DataLang.Prog) (state : State C F)
    (yesClock : (evaluate yes state).2.clock ≤ state.clock)
    (noClock : (evaluate no state).2.clock ≤ state.clock) :
    (evaluate (.ifThenElse name yes no) state).2.clock ≤ state.clock := by
  rw [evaluate]
  split
  · simp
  · split
    · exact yesClock
    · split
      · exact noClock
      · simp

/-- A trailing skip does not change a result whose evaluator clock is already
known to be bounded. -/
theorem evaluate_seq_skip_of_clock {C F : Type} (program : DataLang.Prog) (state : State C F)
    (clockBound : (evaluate program state).2.clock ≤ state.clock) :
    evaluate (.seq program .skip) state = evaluate program state := by
  cases run : evaluate program state with
  | mk result next =>
    simp only [run] at clockBound
    cases result <;> simp [evaluate, run, fixClock, Nat.min_eq_right clockBound]

end Flapjack.Compiler.Backend.DataSem
