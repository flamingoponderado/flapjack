import Flapjack.Compiler.Backend.BvlToBvi.Proofs.VarList
import Flapjack.Compiler.Backend.Semantics.BvlProps.VarBound

/-! Environment independence for bound BVL expressions. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem
open Flapjack.Compiler.Backend.BvlProps (bVarBound)

/-- An expression whose variables are bounded by the initial environment
cannot observe an appended environment. This is untagged pending source and
evaluator correspondence review. -/
theorem evaluate_bVarBound {C F : Type} (xs : List Bvl.Exp) (env extra : List Value)
    (state : State C F) (bound : bVarBound env.length xs) :
    evaluate xs (env ++ extra) state = evaluate xs env state := by
  cases xs with
  | nil => simp [evaluate]
  | cons first rest =>
    cases rest with
    | cons second tail =>
      simp only [bVarBound] at bound
      rw [evaluate, evaluate, fixClock_evaluate, fixClock_evaluate]
      rw [evaluate_bVarBound [first] env extra state bound.1]
      cases headRun : evaluate [first] env state with
      | mk headResult next =>
        cases headResult with
        | err error => rfl
        | val values =>
          dsimp only
          rw [evaluate_bVarBound (second :: tail) env extra next bound.2]
    | nil =>
      cases first with
      | var index =>
        simp only [bVarBound] at bound
        simp [evaluate, List.getElem?_append_left bound]
      | force location index =>
        simp only [bVarBound] at bound
        simp [evaluate, List.getElem?_append_left bound]
      | tick body =>
        simp only [bVarBound] at bound
        rw [evaluate, evaluate]
        by_cases zero : state.clock = 0
        · simp [zero]
        · simp only [zero, ↓reduceIte]
          exact evaluate_bVarBound [body] env extra (decClock 1 state) bound
      | raise body =>
        simp only [bVarBound] at bound
        rw [evaluate, evaluate, evaluate_bVarBound [body] env extra state bound]
      | op op args =>
        simp only [bVarBound] at bound
        rw [evaluate, evaluate, fixClock_evaluate, fixClock_evaluate,
          evaluate_bVarBound args env extra state bound]
      | call ticks dest args =>
        simp only [bVarBound] at bound
        rw [evaluate, evaluate, fixClock_evaluate, fixClock_evaluate,
          evaluate_bVarBound args env extra state bound]
      | ifThenElse condition yes no =>
        simp only [bVarBound] at bound
        rw [evaluate, evaluate, fixClock_evaluate, fixClock_evaluate,
          evaluate_bVarBound [condition] env extra state bound.1]
        cases conditionRun : evaluate [condition] env state with
        | mk conditionResult next =>
          cases conditionResult with
          | err error => rfl
          | val values =>
            dsimp only
            rw [evaluate_bVarBound [yes] env extra next bound.2.1,
              evaluate_bVarBound [no] env extra next bound.2.2]
      | «let» bindings body =>
        simp only [bVarBound] at bound
        rw [evaluate, evaluate, fixClock_evaluate, fixClock_evaluate,
          evaluate_bVarBound bindings env extra state bound.1]
        cases bindingsRun : evaluate bindings env state with
        | mk bindingsResult next =>
          cases bindingsResult with
          | err error => rfl
          | val values =>
            dsimp only
            have length := evaluate_length bindings env state next values bindingsRun
            have bodyBound : bVarBound (values ++ env).length [body] := by
              simpa [List.length_append, length, Nat.add_comm] using bound.2
            rw [← List.append_assoc]
            exact evaluate_bVarBound [body] (values ++ env) extra next bodyBound
      | handle body handler =>
        simp only [bVarBound] at bound
        rw [evaluate, evaluate, fixClock_evaluate, fixClock_evaluate,
          evaluate_bVarBound [body] env extra state bound.1]
        cases bodyRun : evaluate [body] env state with
        | mk bodyResult next =>
          cases bodyResult with
          | val values => rfl
          | err error =>
            cases error with
            | abort reason => rfl
            | raise value =>
              dsimp only
              have handlerBound : bVarBound (value :: env).length [handler] := by
                simpa [Nat.add_comm] using bound.2
              exact evaluate_bVarBound [handler] (value :: env) extra next handlerBound
termination_by expsWeight xs
decreasing_by
  all_goals subst_vars
  all_goals simp only [expsWeight, expWeight]
  all_goals try (have := expWeight_pos second)
  all_goals omega

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
