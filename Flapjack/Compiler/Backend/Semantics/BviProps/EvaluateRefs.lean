import Flapjack.Compiler.Backend.Semantics.BviProps.ApplyRefs
import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateClockFull

/-! Reference-domain growth during BVI evaluation. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.Compiler.Backend.BviSem

/-- Flapjack infrastructure: inclusion of reference domains. -/
def refsGrowth {C F : Type} (before after : BviState C F) : Prop :=
  ∀ key, before.refs.lookup key ≠ none → after.refs.lookup key ≠ none

private theorem refsGrowth_refl {C F : Type} (s : BviState C F) : refsGrowth s s :=
  fun _ present => present

private theorem refsGrowth_trans {C F : Type} {a b c : BviState C F}
    (ab : refsGrowth a b) (bc : refsGrowth b c) : refsGrowth a c :=
  fun key present => bc key (ab key present)

private theorem refsGrowth_decClock {C F : Type} (n : Nat) (s : BviState C F) :
    refsGrowth s (decClock n s) := refsGrowth_refl s

private theorem refsGrowth_doApp {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s t : BviState C F) (value : Value) (run : doApp op args s = .val (value, t)) :
    refsGrowth s t := doApp_refs_mono op args s t value run

/-- Flapjack infrastructure: BVI evaluation preserves reference-domain
membership. It remains untagged until the BVI evaluator is source-reviewed. -/
theorem evaluate_refs_mono {C F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (state : BviState C F) : refsGrowth state (evaluate expressions env state).2 := by
  have allRanks : ∀ clock weight : Nat, ∀ (expressions : List Bvi.Exp)
      (env : List Value) (state : BviState C F),
      state.clock = clock → expsWeight expressions = weight →
      refsGrowth state (evaluate expressions env state).2 := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List Bvi.Exp) (env : List Value) (state : BviState C F),
            state.clock ≤ clock → expsWeight expressions < weight →
            refsGrowth state (evaluate expressions env state).2 := by
          intro expressions env state clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl
          · exact weightIH (expsWeight expressions) weightLt expressions env state clockEq rfl
        have smaller : ∀ (expressions : List Bvi.Exp) (env : List Value) (state : BviState C F),
            state.clock < clock → refsGrowth state (evaluate expressions env state).2 := by
          intro expressions env state clockLt
          exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl
        intro expressions env state stateClock measure
        cases expressions with
        | nil => simpa [evaluate] using refsGrowth_refl state
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
                  cases result <;> exact refsGrowth_trans headGrowth tailGrowth
          | nil =>
            cases first with
            | var index =>
              rw [evaluate]
              split <;> simpa using refsGrowth_refl state
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
                  · exact refsGrowth_trans firstGrowth (exprIH [yes] env next (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢; omega))
                  · exact refsGrowth_trans firstGrowth (exprIH [no] env next (by omega) (by
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
                  exact refsGrowth_trans firstGrowth (exprIH [body] (values ++ env) next (by omega) (by
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
              · simpa using refsGrowth_refl state
              · have bodyGrowth := smaller [body] env (decClock 1 state) (by
                  simp only [decClock]; omega)
                exact refsGrowth_trans (refsGrowth_decClock 1 state) bodyGrowth
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
                    simpa [appRun] using refsGrowth_trans firstGrowth
                      (refsGrowth_doApp op values.reverse next last value appRun)
            | force location index =>
              rw [evaluate]
              split
              · simpa using refsGrowth_refl state
              · split
                · simpa using refsGrowth_refl state
                · simpa using refsGrowth_refl state
                · simpa using refsGrowth_refl state
                · split
                  · simpa using refsGrowth_refl state
                  · rename_i args body found
                    split
                    · simp [refsGrowth]
                    · have bodyGrowth := smaller [body] args (decClock 1 state) (by
                        simp only [decClock]; omega)
                      cases bodyRun : evaluate [body] args (decClock 1 state) with
                      | mk result next =>
                        simp only [bodyRun] at bodyGrowth
                        cases result with
                        | val values => exact refsGrowth_trans (refsGrowth_decClock 1 state) bodyGrowth
                        | err error =>
                          cases error with
                          | abort reason => exact refsGrowth_trans (refsGrowth_decClock 1 state) bodyGrowth
                          | raise payload =>
                            cases payload <;> simpa using refsGrowth_trans (refsGrowth_decClock 1 state) bodyGrowth
            | call ticks dest args handler =>
              have argsGrowth := exprIH args env state (by omega) (by
                cases handler <;> simp only [expsWeight, expWeight] at measure ⊢ <;> omega)
              have argsClock := evaluate_clock_le args env state
              rw [evaluate]
              split
              · simpa using refsGrowth_refl state
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
                      · simpa [refsGrowth] using argsGrowth
                      · have calledGrowth := smaller [body] selected (decClock (ticks + 1) next) (by
                          simp only [decClock]; omega)
                        have calledClock := evaluate_clock_le [body] selected (decClock (ticks + 1) next)
                        rw [fixClock_evaluate]
                        cases callRun : evaluate [body] selected (decClock (ticks + 1) next) with
                        | mk callResult called =>
                          simp only [callRun] at calledGrowth calledClock
                          have beforeHandler := refsGrowth_trans argsGrowth
                            (refsGrowth_trans (refsGrowth_decClock (ticks + 1) next) calledGrowth)
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
                                    | val values => exact refsGrowth_trans beforeHandler handlerGrowth
                                    | err error =>
                                      cases error with
                                      | abort reason => exact refsGrowth_trans beforeHandler handlerGrowth
                                      | raise payload =>
                                        cases payload <;> exact refsGrowth_trans beforeHandler handlerGrowth
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
                    · simpa [refsGrowth] using argsGrowth
                    · have calledGrowth := smaller [callee] selected (decClock (ticks + 1) next) (by
                        simp only [decClock]; omega)
                      have calledClock := evaluate_clock_le [callee] selected (decClock (ticks + 1) next)
                      rw [fixClock_evaluate]
                      cases callRun : evaluate [callee] selected (decClock (ticks + 1) next) with
                      | mk callResult called =>
                        simp only [callRun] at calledGrowth calledClock
                        have beforeBody := refsGrowth_trans argsGrowth
                          (refsGrowth_trans (refsGrowth_decClock (ticks + 1) next) calledGrowth)
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
                                exact refsGrowth_trans beforeBody bodyGrowth
                              · exact beforeBody
  exact allRanks state.clock (expsWeight expressions) expressions env state rfl rfl


/-- Flapjack infrastructure: a completed BVI evaluation preserves reference
keys. -/
theorem evaluate_refs_subset {C F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (s t : BviState C F) (result : BviResult)
    (run : evaluate expressions env s = (result, t)) : s.refs.domain ⊆ t.refs.domain := by
  have growth := evaluate_refs_mono expressions env s
  have preserved : refsGrowth s t := by simpa [run] using growth
  intro key present
  exact preserved key present

end Flapjack.Compiler.Backend.BviProps
