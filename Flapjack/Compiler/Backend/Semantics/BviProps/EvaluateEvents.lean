import Flapjack.Compiler.Backend.Semantics.BviProps.ApplyEvents
import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateClockFull

/-! Event-prefix preservation by the BVI evaluator. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.Compiler.Backend.BviSem

/-- I/O events observed before evaluation form a prefix of those after it. -/
def eventGrowth {C F : Type} (before after : BviState C F) : Prop :=
  before.ffi.ioEvents <+: after.ffi.ioEvents

/-- The event-prefix relation is reflexive. -/
theorem eventGrowth_refl {C F : Type} (s : BviState C F) : eventGrowth s s := List.prefix_refl _

/-- The event-prefix relation composes. -/
theorem eventGrowth_trans {C F : Type} {a b c : BviState C F}
    (ab : eventGrowth a b) (bc : eventGrowth b c) : eventGrowth a c := ab.trans bc

/-- Decreasing the clock does not change I/O events. -/
theorem eventGrowth_decClock {C F : Type} (n : Nat) (s : BviState C F) :
    eventGrowth s (decClock n s) := eventGrowth_refl s

/-- A successful primitive application extends the I/O trace. -/
theorem eventGrowth_doApp {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s t : BviState C F) (value : Value) (run : doApp op args s = .val (value, t)) :
    eventGrowth s t := doApp_ioEvents_prefix op args s t value run

/-- Evaluation extends the I/O trace. Untagged pending BVI evaluator review. -/
theorem evaluate_ioEvents_prefix {C F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (state : BviState C F) : eventGrowth state (evaluate expressions env state).2 := by
  have allRanks : ∀ clock weight : Nat, ∀ (expressions : List Bvi.Exp)
      (env : List Value) (state : BviState C F),
      state.clock = clock → expsWeight expressions = weight →
      eventGrowth state (evaluate expressions env state).2 := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List Bvi.Exp) (env : List Value) (state : BviState C F),
            state.clock ≤ clock → expsWeight expressions < weight →
            eventGrowth state (evaluate expressions env state).2 := by
          intro expressions env state clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl
          · exact weightIH (expsWeight expressions) weightLt expressions env state clockEq rfl
        have smaller : ∀ (expressions : List Bvi.Exp) (env : List Value) (state : BviState C F),
            state.clock < clock → eventGrowth state (evaluate expressions env state).2 := by
          intro expressions env state clockLt
          exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl
        intro expressions env state stateClock measure
        cases expressions with
        | nil => simpa [evaluate] using eventGrowth_refl state
        | cons first rest =>
          cases rest with
          | cons second tail =>
            have headGrowth := exprIH [first] env state (by omega) (by
              simp only [expsWeight] at measure ⊢; omega)
            have headClock := evaluate_clock_le [first] env state
            rw [evaluate, fixClock_evaluate]
            cases headRun : evaluate [first] env state with
            | mk result next =>
              simp only [headRun] at headGrowth headClock
              cases result with
              | err error => exact headGrowth
              | val values =>
                have tailGrowth := exprIH (second :: tail) env next (by omega) (by
                  simp only [expsWeight] at measure ⊢; omega)
                cases tailRun : evaluate (second :: tail) env next with
                | mk result last =>
                  simp only [tailRun] at tailGrowth
                  cases result <;> exact eventGrowth_trans headGrowth tailGrowth
          | nil =>
            cases first with
            | var index =>
              rw [evaluate]
              split <;> simpa using eventGrowth_refl state
            | ifThenElse condition yes no =>
              have firstGrowth := exprIH [condition] env state (by omega) (by
                simp only [expsWeight, expWeight] at measure ⊢; omega)
              have firstClock := evaluate_clock_le [condition] env state
              rw [evaluate, fixClock_evaluate]
              cases firstRun : evaluate [condition] env state with
              | mk result next =>
                simp only [firstRun] at firstGrowth firstClock
                cases result with
                | err error => exact firstGrowth
                | val values =>
                  dsimp only
                  split
                  · exact firstGrowth
                  · exact eventGrowth_trans firstGrowth (exprIH [yes] env next (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢; omega))
                  · exact eventGrowth_trans firstGrowth (exprIH [no] env next (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢; omega))
            | «let» bindings body =>
              have firstGrowth := exprIH bindings env state (by omega) (by
                simp only [expsWeight, expWeight] at measure ⊢; omega)
              have firstClock := evaluate_clock_le bindings env state
              rw [evaluate, fixClock_evaluate]
              cases firstRun : evaluate bindings env state with
              | mk result next =>
                simp only [firstRun] at firstGrowth firstClock
                cases result with
                | err error => exact firstGrowth
                | val values =>
                  exact eventGrowth_trans firstGrowth (exprIH [body] (values ++ env) next (by omega) (by
                    simp only [expsWeight, expWeight] at measure ⊢; omega))
            | raise body =>
              have bodyGrowth := exprIH [body] env state (by omega) (by
                simp only [expsWeight, expWeight] at measure ⊢; omega)
              rw [evaluate]
              cases bodyRun : evaluate [body] env state with
              | mk result next =>
                simp only [bodyRun] at bodyGrowth
                cases result <;> exact bodyGrowth
            | «return» args =>
              have argsGrowth := exprIH args env state (by omega) (by
                simp only [expsWeight, expWeight] at measure ⊢; omega)
              rw [evaluate]
              cases argsRun : evaluate args env state with
              | mk result next =>
                simp only [argsRun] at argsGrowth
                cases result <;> exact argsGrowth
            | tick body =>
              rw [evaluate]
              split
              · simpa using eventGrowth_refl state
              · have bodyGrowth := smaller [body] env (decClock 1 state) (by
                  simp only [decClock]; omega)
                exact eventGrowth_trans (eventGrowth_decClock 1 state) bodyGrowth
            | op op args =>
              have firstGrowth := exprIH args env state (by omega) (by
                simp only [expsWeight, expWeight] at measure ⊢; omega)
              rw [evaluate, fixClock_evaluate]
              cases firstRun : evaluate args env state with
              | mk result next =>
                simp only [firstRun] at firstGrowth
                cases result with
                | err error => exact firstGrowth
                | val values =>
                  cases appRun : doApp op values.reverse next with
                  | err error => simpa [appRun] using firstGrowth
                  | val pair =>
                    obtain ⟨value, last⟩ := pair
                    simpa [appRun] using eventGrowth_trans firstGrowth
                      (eventGrowth_doApp op values.reverse next last value appRun)
            | force location index =>
              rw [evaluate]
              split
              · simpa using eventGrowth_refl state
              · split
                · simpa using eventGrowth_refl state
                · simpa using eventGrowth_refl state
                · simpa using eventGrowth_refl state
                · split
                  · simpa using eventGrowth_refl state
                  · rename_i args body found
                    split
                    · simp [eventGrowth]
                    · have bodyGrowth := smaller [body] args (decClock 1 state) (by
                        simp only [decClock]; omega)
                      cases bodyRun : evaluate [body] args (decClock 1 state) with
                      | mk result next =>
                        simp only [bodyRun] at bodyGrowth
                        cases result with
                        | val values => exact eventGrowth_trans (eventGrowth_decClock 1 state) bodyGrowth
                        | err error =>
                          cases error with
                          | abort reason => exact eventGrowth_trans (eventGrowth_decClock 1 state) bodyGrowth
                          | raise payload =>
                            cases payload <;> simpa using eventGrowth_trans (eventGrowth_decClock 1 state) bodyGrowth
            | call ticks dest args handler =>
              have argsGrowth := exprIH args env state (by omega) (by
                cases handler <;> simp only [expsWeight, expWeight] at measure ⊢ <;> omega)
              have argsClock := evaluate_clock_le args env state
              rw [evaluate]
              split
              · simpa using eventGrowth_refl state
              · rw [fixClock_evaluate]
                cases argsRun : evaluate args env state with
                | mk result next =>
                  simp only [argsRun] at argsGrowth argsClock
                  cases result with
                  | err error => exact argsGrowth
                  | val values =>
                    dsimp only
                    split
                    · exact argsGrowth
                    · rename_i selected body found
                      split
                      · simpa [eventGrowth] using argsGrowth
                      · have calledGrowth := smaller [body] selected (decClock (ticks + 1) next) (by
                          simp only [decClock]; omega)
                        have calledClock := evaluate_clock_le [body] selected (decClock (ticks + 1) next)
                        rw [fixClock_evaluate]
                        cases callRun : evaluate [body] selected (decClock (ticks + 1) next) with
                        | mk callResult called =>
                          simp only [callRun] at calledGrowth calledClock
                          have beforeHandler := eventGrowth_trans argsGrowth
                            (eventGrowth_trans (eventGrowth_decClock (ticks + 1) next) calledGrowth)
                          cases callResult with
                          | val values => exact beforeHandler
                          | err error =>
                            cases error with
                            | abort reason => exact beforeHandler
                            | raise payload =>
                              cases payload with
                              | ret values => exact beforeHandler
                              | exn value =>
                                cases handler with
                                | none => exact beforeHandler
                                | some handler =>
                                  dsimp only
                                  have handlerGrowth := smaller [handler] (value :: env) called (by
                                    simp only [decClock] at calledClock; omega)
                                  cases handlerRun : evaluate [handler] (value :: env) called with
                                  | mk handledResult final =>
                                    simp only [handlerRun] at handlerGrowth
                                    cases handledResult with
                                    | val values => exact eventGrowth_trans beforeHandler handlerGrowth
                                    | err error =>
                                      cases error with
                                      | abort reason => exact eventGrowth_trans beforeHandler handlerGrowth
                                      | raise payload =>
                                        cases payload <;> exact eventGrowth_trans beforeHandler handlerGrowth
            | letCall rets ticks dest args body =>
              have argsGrowth := exprIH args env state (by omega) (by
                simp only [expsWeight, expWeight] at measure ⊢; omega)
              have argsClock := evaluate_clock_le args env state
              rw [evaluate, fixClock_evaluate]
              cases argsRun : evaluate args env state with
              | mk result next =>
                simp only [argsRun] at argsGrowth argsClock
                cases result with
                | err error => exact argsGrowth
                | val values =>
                  dsimp only
                  split
                  · exact argsGrowth
                  · rename_i selected callee found
                    split
                    · simpa [eventGrowth] using argsGrowth
                    · have calledGrowth := smaller [callee] selected (decClock (ticks + 1) next) (by
                        simp only [decClock]; omega)
                      have calledClock := evaluate_clock_le [callee] selected (decClock (ticks + 1) next)
                      rw [fixClock_evaluate]
                      cases callRun : evaluate [callee] selected (decClock (ticks + 1) next) with
                      | mk callResult called =>
                        simp only [callRun] at calledGrowth calledClock
                        have beforeBody := eventGrowth_trans argsGrowth
                          (eventGrowth_trans (eventGrowth_decClock (ticks + 1) next) calledGrowth)
                        cases callResult with
                        | val values => exact beforeBody
                        | err error =>
                          cases error with
                          | abort reason => exact beforeBody
                          | raise payload =>
                            cases payload with
                            | exn value => exact beforeBody
                            | ret values =>
                              dsimp only
                              split
                              · have bodyGrowth := smaller [body] (values ++ env) called (by
                                  simp only [decClock] at calledClock; omega)
                                exact eventGrowth_trans beforeBody bodyGrowth
                              · exact beforeBody
  exact allRanks state.clock (expsWeight expressions) expressions env state rfl rfl

end Flapjack.Compiler.Backend.BviProps
