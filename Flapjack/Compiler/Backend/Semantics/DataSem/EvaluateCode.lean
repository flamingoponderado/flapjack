import Flapjack.Compiler.Backend.Semantics.DataSem.EvaluateClock

/-! Code-table invariants for composing data-language evaluations. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Restoring an environment leaves the code table intact. -/
theorem popEnv_code {C F : Type} (state next : State C F) (run : popEnv state = some next) :
    next.code = state.code := by
  unfold popEnv at run
  split at run <;> simp_all
  all_goals subst next; rfl

/-- Exception unwinding leaves the code table intact. -/
theorem jumpExc_code {C F : Type} (state next : State C F) (run : jumpExc state = some next) :
    next.code = state.code := by
  unfold jumpExc at run
  split at run
  · split at run <;> simp_all
    subst next
    rfl
  · simp at run

/-- Cutting locals does not change the code table. -/
theorem cutStateOpt_code {C F : Type} (live : Option NumSet) (state next : State C F)
    (run : cutStateOpt live state = some next) : next.code = state.code := by
  cases live with
  | none => simp [cutStateOpt] at run; subst next; rfl
  | some names =>
    cases cut : cutEnv names state.locals with
    | none => simp [cutStateOpt, cutState, cut] at run
    | some env => simp [cutStateOpt, cutState, cut] at run; subst next; rfl

/-- An assignment preserves code when its successful primitive application
preserves code; the premise excludes no errors and permits installation to be
handled separately. -/
theorem evaluate_assign_code_step {C F : Type} (dest : Nat) (op : ClosLang.Op) (names : List Nat)
    (live : Option NumSet) (state : State C F)
    (appCode : ∀ (values : List Value) (before after : State C F) (value : Value),
      before.code = state.code → doApp op values before = .val (value, after) → after.code = state.code) :
    (evaluate (.assign dest op names live) state).2.code = state.code := by
  by_cases invalid : (DataLang.opRequiresNames op == live.isNone) = true
  · simp [evaluate, invalid]
  · cases read : getVars names state.locals with
    | none => simp [evaluate, invalid, read]
    | some args =>
      cases cut : cutStateOpt live state with
      | none => simp [evaluate, invalid, read, cut]
      | some prepared =>
        have cutCode := cutStateOpt_code live state prepared cut
        cases app : doApp op args prepared with
        | err error => simp [evaluate, invalid, read, cut, app, flushState, installSfs, cutCode]
        | val pair =>
          obtain ⟨value, applied⟩ := pair
          have code := appCode args prepared applied value cutCode app
          simp [evaluate, invalid, read, cut, app, setVar, installSfs, code]

/-- A move leaves the code table unchanged, even on a failed lookup. -/
theorem evaluate_move_code {C F : Type} (dest src : Nat) (state : State C F) :
    (evaluate (.move dest src) state).2.code = state.code := by
  simp only [evaluate]
  split <;> simp [setVar]

/-- A tick leaves the code table unchanged, including on timeout. -/
theorem evaluate_tick_code {C F : Type} (state : State C F) :
    (evaluate .tick state).2.code = state.code := by
  simp [evaluate, decClock]
  split <;> simp_all [flushState]

/-- A return leaves the code table unchanged. -/
theorem evaluate_return_code {C F : Type} (names : List Nat) (state : State C F) :
    (evaluate (.return names) state).2.code = state.code := by
  simp only [evaluate]
  split <;> simp [flushState]

/-- Raising either fails or unwinds without changing the code table. -/
theorem evaluate_raise_code {C F : Type} (name : Nat) (state : State C F) :
    (evaluate (.raise name) state).2.code = state.code := by
  cases read : getVar name state.locals with
  | none => simp [evaluate, read]
  | some value =>
    cases jump : jumpExc state with
    | none => simp [evaluate, read, jump]
    | some next => simp [evaluate, read, jump, jumpExc_code state next jump]

/-- A sequence preserves the code table if both its components do. -/
theorem evaluate_seq_code_step {C F : Type} (first second : DataLang.Prog) (state : State C F)
    (firstCode : (evaluate first state).2.code = state.code)
    (secondCode : ∀ mid : State C F, mid.code = state.code →
      (evaluate second mid).2.code = mid.code) :
    (evaluate (.seq first second) state).2.code = state.code := by
  have firstClamped : (fixClock state (evaluate first state)).2.code = state.code := by
    simpa [fixClock] using firstCode
  rw [evaluate]
  generalize run : fixClock state (evaluate first state) = pair at *
  obtain ⟨result, mid⟩ := pair
  change mid.code = state.code at firstClamped
  cases result with
  | some value => exact firstClamped
  | none => exact (secondCode mid firstClamped).trans firstClamped

/-- A conditional preserves the code table if both branches do. -/
theorem evaluate_if_code_step {C F : Type} (name : Nat) (yes no : DataLang.Prog) (state : State C F)
    (yesCode : (evaluate yes state).2.code = state.code)
    (noCode : (evaluate no state).2.code = state.code) :
    (evaluate (.ifThenElse name yes no) state).2.code = state.code := by
  rw [evaluate]
  split
  · simp
  · split
    · exact yesCode
    · split
      · exact noCode
      · simp

/-- A source call preserves its code table when every smaller-clock callee
and handler entered with that table preserves it. Installation is deliberately
not assumed to preserve code; this is a conditional composition lemma. -/
theorem evaluate_call_code_step {C F : Type} (ret : Option (List Nat × NumSet)) (dest : Option Nat)
    (names : List Nat) (handler : Option (Nat × DataLang.Prog)) (state : State C F)
    (bodyCode : ∀ (body : DataLang.Prog) (next : State C F), next.clock < state.clock →
      next.code = state.code → (evaluate body next).2.code = state.code) :
    (evaluate (.call ret dest names handler) state).2.code = state.code := by
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
            have code := bodyCode body entered smaller rfl
            cases called : evaluate body entered with
            | mk result last =>
              simp only [called] at code
              simp only [entered] at called
              cases result <;> simpa [evaluate, read, found, zero, called] using code
      | some pair =>
        obtain ⟨returns, live⟩ := pair
        by_cases nodup : returns.Nodup
        · cases cut : cutEnv live state.locals with
          | none => simp [evaluate, read, found, nodup, cut]
          | some env =>
            by_cases zero : state.clock = 0
            · simp [evaluate, read, found, nodup, cut, zero, callEnv, pushEnv, decClock]
            · let entered := callEnv args size (pushEnv env handler.isSome (decClock state))
              have smaller : entered.clock < state.clock := by
                simp [entered, callEnv, pushEnv, decClock]
                omega
              have code : (fixClock entered (evaluate body entered)).2.code = state.code := by
                simpa [fixClock] using bodyCode body entered smaller rfl
              have clock : (fixClock entered (evaluate body entered)).2.clock < state.clock := by
                simp [fixClock, entered, callEnv, pushEnv, decClock]
                omega
              cases called : fixClock entered (evaluate body entered) with
              | mk result last =>
                simp only [called] at code clock
                simp only [entered] at called
                cases result with
                | none => simpa [evaluate, read, found, nodup, cut, zero, called] using code
                | some outcome =>
                  cases outcome with
                  | val returned =>
                    by_cases length : returned.length = returns.length
                    · cases popped : popEnv last with
                      | none => simpa [evaluate, read, found, nodup, cut, zero, called, length, popped] using code
                      | some final =>
                        have finalCode := popEnv_code last final popped
                        simpa [evaluate, read, found, nodup, cut, zero, called, length, popped, setVars, finalCode] using code
                    · simpa [evaluate, read, found, nodup, cut, zero, called, length] using code
                  | err error =>
                    cases error with
                    | abort reason => simpa [evaluate, read, found, nodup, cut, zero, called] using code
                    | raise value =>
                      cases handler with
                      | none =>
                        simp only [Option.isSome] at called
                        simpa [evaluate, read, found, nodup, cut, zero, called] using code
                      | some handler =>
                        obtain ⟨name, handlerBody⟩ := handler
                        simp only [Option.isSome] at called
                        have handlerCode := bodyCode handlerBody (setVar name value last)
                          (by simpa [setVar] using clock) (by simpa [setVar] using code)
                        simpa [evaluate, read, found, nodup, cut, zero, called] using handlerCode
        · simp [evaluate, read, found, nodup]

end Flapjack.Compiler.Backend.DataSem
