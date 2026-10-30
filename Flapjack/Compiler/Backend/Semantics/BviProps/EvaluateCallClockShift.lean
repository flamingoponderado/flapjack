import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateClockShiftCases

/-! BVI call and continuation clock-extension cases. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BviSem
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)
open Flapjack.Compiler.Backend.BvlSem (Value findCode)

/-- Flapjack induction-hypothesis shape for a dynamically selected BVI body. -/
def bodyClockShift {C F : Type} (limit extra : Nat) : Prop :=
  ∀ (body : Bvi.Exp) (env : List Value) (state next : BviState C F) (result : BviResult),
    state.clock < limit → evaluate [body] env state = (result, next) →
    result ≠ .err (.abort .timeoutError) →
    evaluate [body] env (incClock extra state) = (result, incClock extra next)

/-- Flapjack helper: a call preserves clock extension when its arguments,
callee, and possible handler satisfy their induction hypotheses. -/
theorem evaluate_call_addClock {C F : Type} (ticks : Nat) (dest : Option Nat)
    (args : List Bvi.Exp) (handler : Option Bvi.Exp) (env : List Value)
    (state next : BviState C F) (result : BviResult) (extra : Nat)
    (argsIH : ∀ (argResult : BviResult) (argNext : BviState C F),
      evaluate args env state = (argResult, argNext) → argResult ≠ .err (.abort .timeoutError) →
      evaluate args env (incClock extra state) = (argResult, incClock extra argNext))
    (bodyIH : @bodyClockShift C F state.clock extra)
    (run : evaluate [.call ticks dest args handler] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.call ticks dest args handler] env (incClock extra state) =
      (result, incClock extra next) := by
  by_cases invalid : dest.isNone && handler.isSome
  · simp [evaluate, invalid] at run ⊢
    rcases run with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  · cases argsRun : evaluate args env state with
    | mk argResult argNext =>
      have argBound : argNext.clock ≤ state.clock := by
        have bound := evaluate_clock_le args env state
        simpa [argsRun] using bound
      rw [evaluate] at run
      simp only [invalid, Bool.false_eq_true, ↓reduceIte] at run
      rw [fixClock_evaluate, argsRun] at run
      have argNotTimeout : argResult ≠ .err (.abort .timeoutError) := by
        intro bad
        subst argResult
        simp at run
        exact notTimeout run.1.symm
      have shiftedArgs := argsIH argResult argNext argsRun argNotTimeout
      rw [evaluate]
      simp only [invalid, Bool.false_eq_true, ↓reduceIte]
      rw [fixClock_evaluate, shiftedArgs]
      cases argResult with
      | err error => simp_all [incClock]
      | val values =>
        cases found : findCode dest values argNext.code with
        | none =>
          simp [found, incClock] at run ⊢
          rcases run with ⟨rfl, rfl⟩
          simp
        | some selected =>
          obtain ⟨callValues, body⟩ := selected
          by_cases timeout : argNext.clock < ticks + 1
          · simp [found, timeout] at run
            exact (notTimeout run.1.symm).elim
          · have shiftedEnough : ¬ argNext.clock + extra < ticks + 1 := by omega
            have smaller : (decClock (ticks + 1) argNext).clock < state.clock := by
              simp only [decClock]
              omega
            have clocks : decClock (ticks + 1) (incClock extra argNext) =
                incClock extra (decClock (ticks + 1) argNext) :=
              decClock_incClock argNext ticks extra timeout
            simp only [found, timeout, ↓reduceIte, fixClock_evaluate] at run
            simp only [incClock, found, shiftedEnough, ↓reduceIte,
              fixClock_evaluate]
            simp only [incClock] at clocks
            rw [clocks]
            cases bodyRun : evaluate [body] callValues (decClock (ticks + 1) argNext) with
            | mk bodyResult bodyNext =>
              rw [bodyRun] at run
              have bodyNotTimeout : bodyResult ≠ .err (.abort .timeoutError) := by
                intro bad
                subst bodyResult
                simp at run
                exact notTimeout run.1.symm
              have shiftedBody := bodyIH body callValues (decClock (ticks + 1) argNext) bodyNext
                bodyResult smaller bodyRun bodyNotTimeout
              simp only [incClock] at shiftedBody
              rw [shiftedBody]
              cases bodyResult with
              | val values => simp_all [incClock]
              | err error =>
                cases error with
                | abort reason => simp_all [incClock]
                | raise payload =>
                  cases payload with
                  | ret values => simp_all [incClock]
                  | exn value =>
                    cases handler with
                    | none => simp_all [incClock]
                    | some handler =>
                      have calledClock : bodyNext.clock < state.clock := by
                        have bound := evaluate_clock_le [body] callValues (decClock (ticks + 1) argNext)
                        simp only [bodyRun] at bound
                        omega
                      cases handlerRun : evaluate [handler] (value :: env) bodyNext with
                      | mk handlerResult handlerNext =>
                        have handlerNotTimeout : handlerResult ≠ .err (.abort .timeoutError) := by
                          intro bad
                          subst handlerResult
                          simp [handlerRun] at run
                          exact notTimeout run.1.symm
                        have shiftedHandler := bodyIH handler (value :: env) bodyNext handlerNext handlerResult
                          calledClock handlerRun handlerNotTimeout
                        simp only [incClock] at shiftedHandler
                        simp only [handlerRun] at run
                        dsimp only
                        rw [shiftedHandler]
                        cases handlerResult with
                        | val values => simp_all
                        | err error =>
                          cases error with
                          | abort reason => simp_all
                          | raise payload => cases payload <;> simp_all

/-- Flapjack helper: a let-call preserves clock extension when its arguments,
callee, and continuation satisfy their induction hypotheses. -/
theorem evaluate_letCall_addClock {C F : Type} (rets ticks dest : Nat)
    (args : List Bvi.Exp) (body : Bvi.Exp) (env : List Value)
    (state next : BviState C F) (result : BviResult) (extra : Nat)
    (argsIH : ∀ (argResult : BviResult) (argNext : BviState C F),
      evaluate args env state = (argResult, argNext) → argResult ≠ .err (.abort .timeoutError) →
      evaluate args env (incClock extra state) = (argResult, incClock extra argNext))
    (bodyIH : @bodyClockShift C F state.clock extra)
    (run : evaluate [.letCall rets ticks dest args body] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.letCall rets ticks dest args body] env (incClock extra state) =
      (result, incClock extra next) := by
  cases argsRun : evaluate args env state with
  | mk argResult argNext =>
    have argBound : argNext.clock ≤ state.clock := by
      have bound := evaluate_clock_le args env state
      simpa [argsRun] using bound
    rw [evaluate, fixClock_evaluate, argsRun] at run
    have argNotTimeout : argResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst argResult
      simp at run
      exact notTimeout run.1.symm
    have shiftedArgs := argsIH argResult argNext argsRun argNotTimeout
    rw [evaluate, fixClock_evaluate, shiftedArgs]
    cases argResult with
    | err error => simp_all [incClock]
    | val values =>
      cases found : findCode (some dest) values argNext.code with
      | none =>
        simp [found, incClock] at run ⊢
        rcases run with ⟨rfl, rfl⟩
        simp
      | some selected =>
        obtain ⟨callValues, callee⟩ := selected
        by_cases timeout : argNext.clock < ticks + 1
        · simp [found, timeout] at run
          exact (notTimeout run.1.symm).elim
        · have shiftedEnough : ¬ argNext.clock + extra < ticks + 1 := by omega
          have smaller : (decClock (ticks + 1) argNext).clock < state.clock := by
            simp only [decClock]
            omega
          have clocks : decClock (ticks + 1) (incClock extra argNext) =
              incClock extra (decClock (ticks + 1) argNext) :=
            decClock_incClock argNext ticks extra timeout
          simp only [found, timeout, ↓reduceIte, fixClock_evaluate] at run
          simp only [incClock, found, shiftedEnough, ↓reduceIte, fixClock_evaluate]
          simp only [incClock] at clocks
          rw [clocks]
          cases bodyRun : evaluate [callee] callValues (decClock (ticks + 1) argNext) with
          | mk bodyResult bodyNext =>
            rw [bodyRun] at run
            have bodyNotTimeout : bodyResult ≠ .err (.abort .timeoutError) := by
              intro bad
              subst bodyResult
              simp at run
              exact notTimeout run.1.symm
            have shiftedBody := bodyIH callee callValues (decClock (ticks + 1) argNext) bodyNext
              bodyResult smaller bodyRun bodyNotTimeout
            simp only [incClock] at shiftedBody
            rw [shiftedBody]
            cases bodyResult with
            | val values => simp_all [incClock]
            | err error =>
              cases error with
              | abort reason => simp_all [incClock]
              | raise payload =>
                cases payload with
                | exn value => simp_all [incClock]
                | ret values =>
                  by_cases arity : values.length = rets
                  · have calledClock : bodyNext.clock < state.clock := by
                      have bound := evaluate_clock_le [callee] callValues (decClock (ticks + 1) argNext)
                      simp only [bodyRun] at bound
                      omega
                    have continuationRun : evaluate [body] (values ++ env) bodyNext = (result, next) := by
                      simpa [arity] using run
                    have shiftedContinuation := bodyIH body (values ++ env) bodyNext next result
                      calledClock continuationRun notTimeout
                    simpa [arity, incClock] using shiftedContinuation
                  · simp_all [incClock]

end Flapjack.Compiler.Backend.BviProps
