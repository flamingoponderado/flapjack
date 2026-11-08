import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyClock
import Flapjack.Misc.ClockWeightInduction

/-! Clock-bound building blocks for data-language evaluation. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Fixing a result's clock cannot exceed the input state's clock. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "fix_clock_IMP"]
theorem fixClock_imp {C F D G R : Type} (state : State C F) (result : R × State D G)
    (value : R) (next : State D G) (fixed : fixClock state result = (value, next)) :
    next.clock ≤ state.clock := by
  cases result with
  | mk resultValue resultState =>
    simp only [fixClock, Prod.mk.injEq] at fixed
    obtain ⟨_, rfl⟩ := fixed
    exact Nat.min_le_left _ _

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

/-- An unevaluated force enters its code with a strictly smaller clock; the
already evaluated and timeout branches preserve or decrease it directly. -/
theorem evaluate_force_clock_step {C F : Type} (ret : Option (Nat × NumSet)) (label src : Nat)
    (state : State C F)
    (bodyClock : ∀ (body : DataLang.Prog) (next : State C F), next.clock < state.clock →
      (evaluate body next).2.clock ≤ next.clock) :
    (evaluate (.force ret label src) state).2.clock ≤ state.clock := by
  cases read : getVar src state.locals with
  | none => simp [evaluate, read]
  | some thunk =>
    cases inspect : destThunk thunk state.refs with
    | badRef => simp [evaluate, read, inspect]
    | notThunk => simp [evaluate, read, inspect]
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        cases ret with
        | none => simp [evaluate, read, inspect, flushState]
        | some pair =>
          obtain ⟨dest, names⟩ := pair
          cases cut : cutEnv names state.locals <;> simp [evaluate, read, inspect, cut, setVar]
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none => simp [evaluate, read, inspect, found]
        | some triple =>
          obtain ⟨args, body, size⟩ := triple
          cases ret with
          | none =>
            by_cases zero : state.clock = 0
            · simp [evaluate, read, inspect, found, zero]
            · let entered := callEnv args size (decClock state)
              have smaller : entered.clock < state.clock := by
                simp [entered, callEnv, decClock]
                omega
              have bound := Nat.le_trans (bodyClock body entered smaller) (Nat.le_of_lt smaller)
              cases called : evaluate body entered with
              | mk result last =>
                simp only [called] at bound
                simp only [entered] at called
                cases result <;> simpa [evaluate, read, inspect, found, zero, called] using bound
          | some pair =>
            obtain ⟨dest, names⟩ := pair
            cases cut : cutEnv names state.locals with
            | none => simp [evaluate, read, inspect, found, cut]
            | some env =>
              by_cases zero : state.clock = 0
              · simp [evaluate, read, inspect, found, cut, zero, callEnv, pushEnv, decClock]
              · let entered := callEnv args size (pushEnv env false (decClock state))
                have bound : (fixClock entered (evaluate body entered)).2.clock ≤ state.clock := by
                  simp [fixClock, entered, callEnv, pushEnv, decClock]
                  omega
                cases called : fixClock entered (evaluate body entered) with
                | mk result last =>
                  simp only [called] at bound
                  simp only [entered] at called
                  cases result with
                  | none => simpa [evaluate, read, inspect, found, cut, zero, called] using bound
                  | some outcome =>
                    cases outcome with
                    | err error => simpa [evaluate, read, inspect, found, cut, zero, called] using bound
                    | val values =>
                      cases values with
                      | nil => simpa [evaluate, read, inspect, found, cut, zero, called] using bound
                      | cons result rest =>
                        cases rest with
                        | cons other rest => simpa [evaluate, read, inspect, found, cut, zero, called] using bound
                        | nil =>
                          cases popped : popEnv last with
                          | none => simpa [evaluate, read, inspect, found, cut, zero, called, popped] using bound
                          | some final =>
                            have clock := popEnv_clock last final popped
                            simpa [evaluate, read, inspect, found, cut, zero, called, popped, setVar, clock] using bound

/-- A call either stops directly or enters its callee and handler with a
strictly smaller clock. -/
theorem evaluate_call_clock_step {C F : Type} (ret : Option (List Nat × NumSet)) (dest : Option Nat)
    (names : List Nat) (handler : Option (Nat × DataLang.Prog)) (state : State C F)
    (bodyClock : ∀ (body : DataLang.Prog) (next : State C F), next.clock < state.clock →
      (evaluate body next).2.clock ≤ next.clock) :
    (evaluate (.call ret dest names handler) state).2.clock ≤ state.clock := by
  cases read : getVars names state.locals with
  | none => simp [evaluate, read]
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none => simp [evaluate, read, found]
    | some triple =>
      obtain ⟨args, body, size⟩ := triple
      cases ret with
      | none =>
        cases handler with
        | some h => simp [evaluate, read, found]
        | none =>
          by_cases zero : state.clock = 0
          · simp [evaluate, read, found, zero, flushState]
          · let entered := callEnv args size (decClock state)
            have smaller : entered.clock < state.clock := by
              simp [entered, callEnv, decClock]
              omega
            have bound := Nat.le_trans (bodyClock body entered smaller) (Nat.le_of_lt smaller)
            cases called : evaluate body entered with
            | mk result last =>
              simp only [called] at bound
              simp only [entered] at called
              cases result <;> simpa [evaluate, read, found, zero, called] using bound
      | some pair =>
        obtain ⟨returns, live⟩ := pair
        by_cases nodup : returns.Nodup
        · cases cut : cutEnv live state.locals with
          | none => simp [evaluate, read, found, nodup, cut]
          | some env =>
            by_cases zero : state.clock = 0
            · simp [evaluate, read, found, nodup, cut, zero, callEnv, pushEnv, decClock]
            · let entered := callEnv args size (pushEnv env handler.isSome (decClock state))
              have bound : (fixClock entered (evaluate body entered)).2.clock < state.clock := by
                simp [fixClock, entered, callEnv, pushEnv, decClock]
                omega
              cases called : fixClock entered (evaluate body entered) with
              | mk result last =>
                simp only [called] at bound
                simp only [entered] at called
                cases result with
                | none => simpa [evaluate, read, found, nodup, cut, zero, called] using Nat.le_of_lt bound
                | some outcome =>
                  cases outcome with
                  | val returned =>
                    by_cases length : returned.length = returns.length
                    · cases popped : popEnv last with
                      | none =>
                        simpa [evaluate, read, found, nodup, cut, zero, called, length, popped] using Nat.le_of_lt bound
                      | some final =>
                        have clock := popEnv_clock last final popped
                        simpa [evaluate, read, found, nodup, cut, zero, called, length, popped, setVars, clock] using
                          Nat.le_of_lt bound
                    · simpa [evaluate, read, found, nodup, cut, zero, called, length] using Nat.le_of_lt bound
                  | err error =>
                    cases error with
                    | abort reason =>
                      simpa [evaluate, read, found, nodup, cut, zero, called] using Nat.le_of_lt bound
                    | raise value =>
                      cases handler with
                      | none =>
                        simp only [Option.isSome] at called
                        simpa [evaluate, read, found, nodup, cut, zero, called] using Nat.le_of_lt bound
                      | some handler =>
                        obtain ⟨name, handlerBody⟩ := handler
                        simp only [Option.isSome] at called
                        have handlerBound := bodyClock handlerBody (setVar name value last) (by simpa [setVar] using bound)
                        have finalBound : (evaluate handlerBody (setVar name value last)).2.clock ≤ state.clock :=
                          Nat.le_trans handlerBound (Nat.le_of_lt (by simpa [setVar] using bound))
                        simpa [evaluate, read, found, nodup, cut, zero, called] using finalBound
        · simp [evaluate, read, found, nodup]

/-- Evaluation does not increase the data-language clock. This unconditional
form is Flapjack infrastructure used to prove the HOL-shaped theorem. -/
theorem evaluate_clock_le {C F : Type} (program : DataLang.Prog) (state : State C F) :
    (evaluate program state).2.clock ≤ state.clock := by
  refine clockWeightInduction (α := DataLang.Prog) (σ := State C F) (·.clock) sizeOf
    (motive := fun program state => (evaluate program state).2.clock ≤ state.clock) ?_ program state
  intro program state exprIH smaller
  cases program with
  | skip => simp [evaluate]
  | move dest src => exact evaluate_move_clock dest src state
  | assign dest op names live => exact evaluate_assign_clock dest op names live state
  | tick => exact evaluate_tick_clock state
  | makeSpace amount names => exact evaluate_makeSpace_clock amount names state
  | raise name => exact evaluate_raise_clock name state
  | «return» names => exact evaluate_return_clock names state
  | seq first second =>
    apply evaluate_seq_clock_step first second state
    intro mid bound
    apply exprIH second mid (by omega)
    simp only [DataLang.Prog.seq.sizeOf_spec] at ⊢
    omega
  | ifThenElse name yes no =>
    apply evaluate_if_clock_step name yes no state
    · apply exprIH yes state (by omega)
      simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at ⊢
      omega
    · apply exprIH no state (by omega)
      simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at ⊢
      omega
  | force ret label src =>
    apply evaluate_force_clock_step ret label src state
    intro body next bound
    exact smaller body next (by omega)
  | call ret dest names handler =>
    apply evaluate_call_clock_step ret dest names handler state
    intro body next bound
    exact smaller body next (by omega)

/-- A completed evaluation does not increase the clock. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "evaluate_clock"]
theorem evaluateClock {C F : Type} (program : DataLang.Prog) (state : State C F)
    (result : Option (Result (List Value) Value)) (next : State C F)
    (run : evaluate program state = (result, next)) : next.clock ≤ state.clock := by
  have bound := evaluate_clock_le program state
  simpa only [run] using bound

/-- The evaluator's termination clamp is inert on a completed evaluation. -/
theorem fixClock_evaluate {C F : Type} (program : DataLang.Prog) (state : State C F) :
    fixClock state (evaluate program state) = evaluate program state := by
  have bound := evaluate_clock_le program state
  cases run : evaluate program state with
  | mk result next =>
    simp only [run] at bound
    simp [fixClock, Nat.min_eq_right bound]

/-- The HOL clock clamp is inert on an evaluation result. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "fix_clock_evaluate"]
theorem fixClockEvaluate {C F : Type} (state : State C F) (program : DataLang.Prog) :
    fixClock state (evaluate program state) = evaluate program state :=
  fixClock_evaluate program state

/-- A trailing skip does not change a result whose evaluator clock is already
known to be bounded. -/
theorem evaluate_seq_skip_of_clock {C F : Type} (program : DataLang.Prog) (state : State C F)
    (clockBound : (evaluate program state).2.clock ≤ state.clock) :
    evaluate (.seq program .skip) state = evaluate program state := by
  cases run : evaluate program state with
  | mk result next =>
    simp only [run] at clockBound
    cases result <;> simp [evaluate, run, fixClock, Nat.min_eq_right clockBound]

/-- A trailing skip does not change a data-language evaluation. This is
untagged while the evaluator correspondence is under review. -/
theorem evaluate_seq_skip {C F : Type} (program : DataLang.Prog) (state : State C F) :
    evaluate (.seq program .skip) state = evaluate program state :=
  evaluate_seq_skip_of_clock program state (evaluate_clock_le program state)

end Flapjack.Compiler.Backend.DataSem
