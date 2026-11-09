module

public import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateCallClockShift
public import Flapjack.Misc.ClockWeightInduction

@[expose] public section

/-! BVI evaluator clock extension. The evaluator and dispatcher remain pending source review. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BviSem
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Flapjack invariant: non-timeout evaluation is stable under added clock. -/
theorem evaluate_addClock {C F : Type} (expressions : List Bvi.Exp)
    (env : List Value) (state next : BviState C F)
    (result : BviResult) (extra : Nat)
    (run : evaluate expressions env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate expressions env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  refine clockWeightInduction (α := List Bvi.Exp) (σ := BviState C F) (·.clock) expsWeight
    (motive := fun expressions state => ∀ env next result,
      evaluate expressions env state = (result, next) → result ≠ .err (.abort .timeoutError) →
      ∀ extra, evaluate expressions env { state with clock := state.clock + extra } =
        (result, { next with clock := next.clock + extra })) ?_
    expressions state env next result run notTimeout extra
  intro expressions state exprIH₀ smaller₀
  have exprIH := fun (es : List Bvi.Exp) (env' : List Value) (s next : BviState C F)
      (result : BviResult) h1 h2 run notTimeout extra =>
    exprIH₀ es s h1 h2 env' next result run notTimeout extra
  have smaller := fun (es : List Bvi.Exp) (env' : List Value) (s next : BviState C F)
      (result : BviResult) h1 run notTimeout extra =>
    smaller₀ es s h1 env' next result run notTimeout extra
  intro env next result run notTimeout extra
  cases expressions with
  | nil => simp [evaluate] at run; rcases run with ⟨rfl, rfl⟩; simp [evaluate]
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply evaluate_list_addClock first second tail env state next result extra ?_ ?_ run
        notTimeout
      · intro childResult childNext childRun childNotTimeout
        apply exprIH [first] env state childNext childResult (by omega) ?_ childRun childNotTimeout
          extra
        simp only [expsWeight] at ⊢; have := expWeight_pos second; omega
      · intro headNext tailNext tailResult bound tailRun tailNotTimeout
        apply exprIH (second :: tail) env headNext tailNext tailResult (by omega) ?_ tailRun
          tailNotTimeout extra
        simp only [expsWeight] at ⊢; omega
    | nil =>
      cases first with
      | var index => exact evaluate_var_addClock index env state next result extra run
      | raise body =>
        apply evaluate_raise_addClock body env state next result extra ?_ run notTimeout
        intro childResult childNext childRun childNotTimeout
        apply exprIH [body] env state childNext childResult (by omega) ?_ childRun childNotTimeout
          extra
        simp only [expsWeight, expWeight] at ⊢; omega
      | tick body =>
        apply evaluate_tick_addClock body env state next result extra ?_ run notTimeout
        intro childResult childNext childRun childNotTimeout
        by_cases zero : state.clock = 0
        · apply exprIH [body] env (decClock 1 state) childNext childResult
            (by simp [decClock]) ?_ childRun childNotTimeout extra
          simp only [expsWeight, expWeight] at ⊢; omega
        · apply smaller [body] env (decClock 1 state) childNext childResult ?_ childRun
            childNotTimeout extra
          simp only [decClock]; omega
      | «let» bindings body =>
        apply evaluate_let_addClock bindings body env state next result extra ?_ ?_ run notTimeout
        · intro childResult childNext childRun childNotTimeout
          apply exprIH bindings env state childNext childResult (by omega) ?_ childRun
            childNotTimeout extra
          simp only [expsWeight, expWeight] at ⊢; omega
        · intro values childNext final bodyResult bound bodyRun bodyNotTimeout
          apply exprIH [body] (values ++ env) childNext final bodyResult (by omega) ?_ bodyRun
            bodyNotTimeout extra
          simp only [expsWeight, expWeight] at ⊢; omega
      | ifThenElse condition yes no =>
        apply evaluate_if_addClock condition yes no env state next result extra ?_ ?_ run notTimeout
        · intro childResult childNext childRun childNotTimeout
          apply exprIH [condition] env state childNext childResult (by omega) ?_ childRun
            childNotTimeout extra
          simp only [expsWeight, expWeight] at ⊢; omega
        · intro choice childNext final bodyResult bound bodyRun bodyNotTimeout
          apply exprIH [if choice then yes else no] env childNext final bodyResult (by omega) ?_
            bodyRun bodyNotTimeout extra
          cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte,
            expsWeight, expWeight] at ⊢ <;> omega
      | op op args =>
        apply evaluate_op_addClock op args env state next result extra ?_ run notTimeout
        intro childResult childNext childRun childNotTimeout
        apply exprIH args env state childNext childResult (by omega) ?_ childRun childNotTimeout
          extra
        simp only [expsWeight, expWeight] at ⊢; omega
      | call ticks location args handler =>
        apply evaluate_call_addClock ticks location args handler env state next result extra ?_ ?_
          run notTimeout
        · intro childResult childNext childRun childNotTimeout
          apply exprIH args env state childNext childResult (by omega) ?_ childRun childNotTimeout
            extra
          cases handler <;> simp only [expsWeight, expWeight] at ⊢ <;> omega
        · intro body values childState childNext childResult bound bodyRun bodyNotTimeout
          exact smaller [body] values childState childNext childResult (by omega) bodyRun
            bodyNotTimeout extra
      | letCall rets ticks dest args body =>
        apply evaluate_letCall_addClock rets ticks dest args body env state next result extra ?_ ?_
          run notTimeout
        · intro childResult childNext childRun childNotTimeout
          apply exprIH args env state childNext childResult (by omega) ?_ childRun childNotTimeout
            extra
          simp only [expsWeight, expWeight] at ⊢; omega
        · intro callee values childState childNext childResult bound bodyRun bodyNotTimeout
          exact smaller [callee] values childState childNext childResult (by omega) bodyRun
            bodyNotTimeout extra
      | «return» args =>
        apply evaluate_return_addClock args env state next result extra ?_ run notTimeout
        intro childResult childNext childRun childNotTimeout
        apply exprIH args env state childNext childResult (by omega) ?_ childRun childNotTimeout
          extra
        simp only [expsWeight, expWeight] at ⊢; omega
      | force location index =>
        apply evaluate_force_addClock location index env state next result extra ?_ run notTimeout
        intro body values childState childNext childResult bound bodyRun bodyNotTimeout
        exact smaller [body] values childState childNext childResult (by omega) bodyRun
          bodyNotTimeout extra

/-- A non-timeout BVI evaluation remains unchanged when clock is added.
This source-shaped statement is untagged pending BVI evaluator correspondence. -/
theorem evaluate_inv_clock {C F : Type} (expressions : List Bvi.Exp)
    (env : List Value) (state next : BviState C F) (result : BviResult) (extra : Nat)
    (run : evaluate expressions env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate expressions env (incClock extra state) = (result, incClock extra next) :=
  evaluate_addClock expressions env state next result extra run notTimeout

end Flapjack.Compiler.Backend.BviProps
