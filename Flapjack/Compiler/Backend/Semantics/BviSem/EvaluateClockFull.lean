import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateClock
import Flapjack.Misc.ClockWeightInduction
/-! Full clock invariant for the source-shaped BVI evaluator. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Forcing an unevaluated thunk consumes one clock tick. -/
theorem evaluate_force_clock_step {C F : Type} (env : List Value) (state : BviState C F)
    (location index : Nat)
    (bodyClock : ∀ (body : Bvi.Exp) (values : List Value) (next : BviState C F),
      next.clock < state.clock → (evaluate [body] values next).2.clock ≤ next.clock) :
    (evaluate [.force location index] env state).2.clock ≤ state.clock := by
  rw [evaluate]
  split
  · simp
  · split
    · simp
    · simp
    · simp
    · split
      · simp
      · rename_i args body found
        split
        · simp
        · have smaller : (decClock 1 state).clock < state.clock := by
            simp only [decClock]
            omega
          have bound := Nat.le_trans (bodyClock body args _ smaller) (Nat.le_of_lt smaller)
          generalize h : evaluate [body] args (decClock 1 state) = evaluated at *
          obtain ⟨result, next⟩ := evaluated
          cases result with
          | val values => exact bound
          | err error => cases error with
            | abort reason => exact bound
            | raise result => cases result <;> simpa using bound

/-- Calls consume clock before entering code or a possible handler. -/
theorem evaluate_call_clock_step {C F : Type} (env : List Value) (state : BviState C F)
    (ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp) (handler : Option Bvi.Exp)
    (bodyClock : ∀ (body : Bvi.Exp) (values : List Value) (next : BviState C F),
      next.clock < state.clock → (evaluate [body] values next).2.clock ≤ next.clock) :
    (evaluate [.call ticks dest args handler] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate args env state)
  rw [evaluate]
  split
  · simp
  · generalize h : fixClock state (evaluate args env state) = evaluated at *
    obtain ⟨result, next⟩ := evaluated
    change next.clock ≤ state.clock at bound
    cases result with
    | err error => exact bound
    | val values =>
      dsimp only
      split
      · simpa using bound
      · rename_i selected body found
        split
        · simp
        · have smaller : (decClock (ticks + 1) next).clock < state.clock := by
            simp only [decClock]
            omega
          have calledBound := fixClock_clock_le (decClock (ticks + 1) next)
            (evaluate [body] selected (decClock (ticks + 1) next))
          generalize hc : fixClock (decClock (ticks + 1) next)
            (evaluate [body] selected (decClock (ticks + 1) next)) = called at *
          obtain ⟨callResult, callFinal⟩ := called
          have calledSmaller : callFinal.clock < state.clock := by
            change callFinal.clock ≤ (decClock (ticks + 1) next).clock at calledBound
            omega
          cases callResult with
          | val values => exact Nat.le_of_lt calledSmaller
          | err error =>
            cases error with
            | abort reason => exact Nat.le_of_lt calledSmaller
            | raise result =>
              cases result with
              | ret values => simpa using Nat.le_of_lt calledSmaller
              | exn value =>
                cases handler with
                | none => exact Nat.le_of_lt calledSmaller
                | some handler =>
                  dsimp only
                  have hbound := Nat.le_trans (bodyClock handler (value :: env) callFinal calledSmaller)
                    (Nat.le_of_lt calledSmaller)
                  generalize hr : evaluate [handler] (value :: env) callFinal = handled at *
                  obtain ⟨handledResult, handledFinal⟩ := handled
                  cases handledResult with
                  | val values => exact hbound
                  | err error => cases error with
                    | abort reason => exact hbound
                    | raise result => cases result <;> simpa using hbound

/-- A let-call consumes clock before entering its callee and continuation. -/
theorem evaluate_letCall_clock_step {C F : Type} (env : List Value) (state : BviState C F)
    (rets ticks dest : Nat) (args : List Bvi.Exp) (body : Bvi.Exp)
    (bodyClock : ∀ (expression : Bvi.Exp) (values : List Value) (next : BviState C F),
      next.clock < state.clock → (evaluate [expression] values next).2.clock ≤ next.clock) :
    (evaluate [.letCall rets ticks dest args body] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate args env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate args env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    dsimp only
    split
    · simpa using bound
    · rename_i selected callee found
      split
      · simp
      · have smaller : (decClock (ticks + 1) next).clock < state.clock := by
          simp only [decClock]
          omega
        have calledBound := fixClock_clock_le (decClock (ticks + 1) next)
          (evaluate [callee] selected (decClock (ticks + 1) next))
        generalize hc : fixClock (decClock (ticks + 1) next)
          (evaluate [callee] selected (decClock (ticks + 1) next)) = called at *
        obtain ⟨callResult, callFinal⟩ := called
        have calledSmaller : callFinal.clock < state.clock := by
          change callFinal.clock ≤ (decClock (ticks + 1) next).clock at calledBound
          omega
        cases callResult with
        | val values => simpa using Nat.le_of_lt calledSmaller
        | err error =>
          cases error with
          | abort reason => exact Nat.le_of_lt calledSmaller
          | raise result =>
            cases result with
            | exn value => exact Nat.le_of_lt calledSmaller
            | ret values =>
              dsimp only
              split
              · exact Nat.le_trans (bodyClock body (values ++ env) callFinal calledSmaller)
                  (Nat.le_of_lt calledSmaller)
              · simpa using Nat.le_of_lt calledSmaller
/-- The source-shaped BVI evaluator does not increase its input clock. This
is a Flapjack invariant; the evaluator itself has not yet been reviewed as an
exact HOL port. -/
theorem evaluate_clock_le {C F : Type} (expressions : List Bvi.Exp) (env : List Value) (state : BviState C F) :
    (evaluate expressions env state).2.clock ≤ state.clock := by
  refine clockWeightInduction (α := List Bvi.Exp) (σ := BviState C F) (·.clock) expsWeight
    (motive := fun expressions state => ∀ env,
      (evaluate expressions env state).2.clock ≤ state.clock) ?_ expressions state env
  intro expressions state exprIH₀ smaller₀
  have exprIH := fun (es : List Bvi.Exp) (env' : List Value) (s : BviState C F)
      h1 h2 => exprIH₀ es s h1 h2 env'
  have smaller := fun (es : List Bvi.Exp) (env' : List Value) (s : BviState C F)
      h => smaller₀ es s h env'
  intro env
  cases expressions with
  | nil => simp [evaluate]
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply evaluate_list_clock_step
      intro next nextBound
      apply exprIH (second :: tail) env next (by omega)
      simp only [expsWeight] at ⊢
      omega
    | nil =>
      cases first with
      | var index => simp [evaluate]; split <;> simp
      | raise body =>
        apply evaluate_raise_clock_step
        apply exprIH [body] env state (by omega)
        simp only [expsWeight, expWeight] at ⊢
        omega
      | «let» bindings body =>
        apply evaluate_let_clock_step
        intro newEnv next nextBound
        apply exprIH [body] newEnv next (by omega)
        simp only [expsWeight, expWeight] at ⊢
        omega
      | ifThenElse condition yes no =>
        apply evaluate_if_clock_step
        · intro next nextBound
          apply exprIH [yes] env next (by omega)
          simp only [expsWeight, expWeight] at ⊢
          omega
        · intro next nextBound
          apply exprIH [no] env next (by omega)
          simp only [expsWeight, expWeight] at ⊢
          omega
      | tick body =>
        apply evaluate_tick_clock_step
        by_cases zero : state.clock = 0
        · apply exprIH [body] env (decClock 1 state) (by simp [decClock])
          simp only [expsWeight, expWeight] at ⊢
          omega
        · apply smaller [body] env (decClock 1 state)
          simp [decClock]
          omega
      | call ticks location args handler =>
        apply evaluate_call_clock_step
        intro body values next nextLt
        exact smaller [body] values next (by omega)
      | letCall rets ticks dest args body =>
        apply evaluate_letCall_clock_step
        intro expression values next nextLt
        exact smaller [expression] values next (by omega)
      | «return» args =>
        apply evaluate_return_clock_step
        apply exprIH args env state (by omega)
        simp only [expsWeight, expWeight] at ⊢
        omega
      | force location index =>
        apply evaluate_force_clock_step
        intro body values next nextLt
        exact smaller [body] values next (by omega)
      | op op args => exact evaluate_op_clock env state op args


/-- The termination-only clock clamp is inert on BVI evaluation results. This
is untagged while the underlying evaluator remains pending source review. -/
theorem fixClock_evaluate {C F : Type} (expressions : List Bvi.Exp)
    (env : List Value) (state : BviState C F) :
    fixClock state (evaluate expressions env state) = evaluate expressions env state := by
  have bound := evaluate_clock_le expressions env state
  cases run : evaluate expressions env state with
  | mk result next =>
    simp only [run] at bound
    simp [fixClock, Nat.min_eq_right bound]

end Flapjack.Compiler.Backend.BviSem
