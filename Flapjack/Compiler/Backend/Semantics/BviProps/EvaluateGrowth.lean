import Flapjack.Compiler.Backend.Semantics.BviProps.ApplyCode
import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateClockFull

/-! Code and global-pointer preservation during BVI evaluation. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.Compiler.Backend.BviSem

/-- Flapjack relation used to compose the two evaluator invariants. -/
def stateGrowth {C F : Type} (before after : BviState C F) : Prop :=
  sptSubspt before.code after.code ∧ (before.global.isSome = true → after.global.isSome = true)

/-- Both invariants are reflexive. -/
theorem stateGrowth_refl {C F : Type} (s : BviState C F) : stateGrowth s s :=
  ⟨fun _ present => ⟨present, rfl⟩, id⟩

/-- Both invariants compose through an intermediate state. -/
theorem stateGrowth_trans {C F : Type} {a b c : BviState C F}
    (ab : stateGrowth a b) (bc : stateGrowth b c) : stateGrowth a c :=
  ⟨sptSubsptTrans a.code b.code c.code ⟨ab.1, bc.1⟩, fun present => bc.2 (ab.2 present)⟩

/-- Clock decrement preserves the observed code and global fields. -/
theorem stateGrowth_decClock {C F : Type} (n : Nat) (s : BviState C F) :
    stateGrowth s (decClock n s) := stateGrowth_refl s

/-- Successful primitive application preserves code and global presence. -/
theorem stateGrowth_doApp {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s t : BviState C F) (value : Value) (run : doApp op args s = .val (value, t)) :
    stateGrowth s t :=
  ⟨doApp_code_mono op args s t value run, doApp_global op args s t value run⟩

/-- The source-shaped evaluator preserves code entries and global presence.
This remains Flapjack infrastructure while the BVI evaluator is unreviewed. -/
theorem evaluate_growth {C F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (state : BviState C F) : stateGrowth state (evaluate expressions env state).2 := by
  have allRanks : ∀ clock weight : Nat, ∀ (expressions : List Bvi.Exp)
      (env : List Value) (state : BviState C F),
      state.clock = clock → expsWeight expressions = weight →
      stateGrowth state (evaluate expressions env state).2 := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List Bvi.Exp) (env : List Value) (state : BviState C F),
            state.clock ≤ clock → expsWeight expressions < weight →
            stateGrowth state (evaluate expressions env state).2 := by
          intro expressions env state clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl
          · exact weightIH (expsWeight expressions) weightLt expressions env state clockEq rfl
        have smaller : ∀ (expressions : List Bvi.Exp) (env : List Value) (state : BviState C F),
            state.clock < clock → stateGrowth state (evaluate expressions env state).2 := by
          intro expressions env state clockLt
          exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl
        intro expressions env state stateClock measure
        cases expressions with
        | nil => simpa [evaluate] using stateGrowth_refl state
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
                  cases result <;> exact stateGrowth_trans headGrowth tailGrowth
          | nil =>
            cases first with
            | var index =>
              rw [evaluate]
              split <;> simpa using stateGrowth_refl state
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
                  · exact stateGrowth_trans firstGrowth (exprIH [yes] env next (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢; omega))
                  · exact stateGrowth_trans firstGrowth (exprIH [no] env next (by omega) (by
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
                  exact stateGrowth_trans firstGrowth (exprIH [body] (values ++ env) next (by omega) (by
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
              · simpa using stateGrowth_refl state
              · have bodyGrowth := smaller [body] env (decClock 1 state) (by
                  simp only [decClock]; omega)
                exact stateGrowth_trans (stateGrowth_decClock 1 state) bodyGrowth
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
                    simpa [appRun] using stateGrowth_trans firstGrowth
                      (stateGrowth_doApp op values.reverse next last value appRun)
            | force location index =>
              rw [evaluate]
              split
              · simpa using stateGrowth_refl state
              · split
                · simpa using stateGrowth_refl state
                · simpa using stateGrowth_refl state
                · simpa using stateGrowth_refl state
                · split
                  · simpa using stateGrowth_refl state
                  · rename_i args body found
                    split
                    · simpa [stateGrowth] using stateGrowth_refl state
                    · have bodyGrowth := smaller [body] args (decClock 1 state) (by
                        simp only [decClock]; omega)
                      cases bodyRun : evaluate [body] args (decClock 1 state) with
                      | mk result next =>
                        simp only [bodyRun] at bodyGrowth
                        cases result with
                        | val values => exact stateGrowth_trans (stateGrowth_decClock 1 state) bodyGrowth
                        | err error =>
                          cases error with
                          | abort reason => exact stateGrowth_trans (stateGrowth_decClock 1 state) bodyGrowth
                          | raise payload =>
                            cases payload <;> simpa using stateGrowth_trans (stateGrowth_decClock 1 state) bodyGrowth
            | call ticks dest args handler =>
              have argsGrowth := exprIH args env state (by omega) (by
                cases handler <;> simp only [expsWeight, expWeight] at measure ⊢ <;> omega)
              have argsClock := evaluate_clock_le args env state
              rw [evaluate]
              split
              · simpa using stateGrowth_refl state
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
                      · simpa [stateGrowth] using argsGrowth
                      · have calledGrowth := smaller [body] selected (decClock (ticks + 1) next) (by
                          simp only [decClock]; omega)
                        have calledClock := evaluate_clock_le [body] selected (decClock (ticks + 1) next)
                        rw [fixClock_evaluate]
                        cases callRun : evaluate [body] selected (decClock (ticks + 1) next) with
                        | mk callResult called =>
                          simp only [callRun] at calledGrowth calledClock
                          have beforeHandler := stateGrowth_trans argsGrowth
                            (stateGrowth_trans (stateGrowth_decClock (ticks + 1) next) calledGrowth)
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
                                    | val values => exact stateGrowth_trans beforeHandler handlerGrowth
                                    | err error =>
                                      cases error with
                                      | abort reason => exact stateGrowth_trans beforeHandler handlerGrowth
                                      | raise payload =>
                                        cases payload <;> exact stateGrowth_trans beforeHandler handlerGrowth
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
                    · simpa [stateGrowth] using argsGrowth
                    · have calledGrowth := smaller [callee] selected (decClock (ticks + 1) next) (by
                        simp only [decClock]; omega)
                      have calledClock := evaluate_clock_le [callee] selected (decClock (ticks + 1) next)
                      rw [fixClock_evaluate]
                      cases callRun : evaluate [callee] selected (decClock (ticks + 1) next) with
                      | mk callResult called =>
                        simp only [callRun] at calledGrowth calledClock
                        have beforeBody := stateGrowth_trans argsGrowth
                          (stateGrowth_trans (stateGrowth_decClock (ticks + 1) next) calledGrowth)
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
                                exact stateGrowth_trans beforeBody bodyGrowth
                              · exact beforeBody
  exact allRanks state.clock (expsWeight expressions) expressions env state rfl rfl

/-- Evaluation preserves existing code entries. This remains untagged until
the BVI evaluator and dispatcher are source-reviewed. -/
theorem evaluate_code_mono {C F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (s t : BviState C F) (result : BviResult)
    (run : evaluate expressions env s = (result, t)) : sptSubspt s.code t.code := by
  have growth := evaluate_growth expressions env s
  simpa [run, stateGrowth] using growth.1

/-- Evaluation preserves an initialized global pointer. This remains
untagged until the BVI evaluator and dispatcher are source-reviewed. -/
theorem evaluate_global_mono {C F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (s t : BviState C F) (result : BviResult)
    (run : evaluate expressions env s = (result, t))
    (present : s.global.isSome = true) : t.global.isSome = true := by
  have growth := evaluate_growth expressions env s
  have preserved : s.global.isSome = true → t.global.isSome = true := by
    simpa [run, stateGrowth] using growth.2
  exact preserved present

end Flapjack.Compiler.Backend.BviProps
