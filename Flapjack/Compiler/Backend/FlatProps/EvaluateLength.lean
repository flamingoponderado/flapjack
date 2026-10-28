import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateClock

/-! Successful result lengths for the clocked flat evaluator. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem

/-- A successful lifted primitive application returns exactly one value. -/
theorem applyResult_length {C F : Type} (state next : State C F) (op : FlatLang.Op)
    (args values : List Value) (run : applyResult state op args = (next, .val values)) :
    values.length = 1 := by
  unfold applyResult at run
  cases call : doApp state op args with
  | none => simp [call] at run
  | some output =>
    obtain ⟨last, result⟩ := output
    cases result <;> simp [call] at run
    rcases run with ⟨_, rfl⟩
    rfl

/-- Successful evaluation produces one value per expression. The evaluator and
its carriers remain pending complete HOL correspondence review. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_length"]
theorem evaluate_length {C F : Type} :
    ∀ (env : Environment Value) (state next : State C F) (expressions : List FlatLang.Exp)
      (values : List Value), evaluate env state expressions = (next, .val values) →
      values.length = expressions.length := by
  have allRanks : ∀ clock weight : Nat,
      ∀ (env : Environment Value) (state next : State C F) (expressions : List FlatLang.Exp)
        (values : List Value), state.clock = clock → expsWeight expressions = weight →
        evaluate env state expressions = (next, .val values) → values.length = expressions.length := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (env : Environment Value) (state next : State C F)
            (expressions : List FlatLang.Exp) (values : List Value),
            state.clock ≤ clock → expsWeight expressions < weight →
            evaluate env state expressions = (next, .val values) → values.length = expressions.length := by
          intro env state next expressions values clockLe weightLt run
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact (clockIH state.clock clockLt) (expsWeight expressions) env state next expressions values rfl rfl run
          · exact (weightIH (expsWeight expressions) weightLt) env state next expressions values clockEq rfl run
        have smallerExpr : ∀ (env : Environment Value) (state next : State C F)
            (body : FlatLang.Exp) (values : List Value), state.clock < clock →
            evaluate env state [body] = (next, .val values) → values.length = 1 := by
          intro env state next body values clockLt run
          simpa using (clockIH state.clock clockLt) (expsWeight [body]) env state next [body] values rfl rfl run
        intro env state next expressions values stateClock measure run
        cases expressions with
        | nil => simp [evaluate] at run; rcases run with ⟨_, rfl⟩; rfl
        | cons first rest =>
          cases rest with
          | cons second tail =>
            have bound := fixClock_clock_le state (evaluate env state [first])
            rw [evaluate] at run
            generalize h : fixClock state (evaluate env state [first]) = firstOutput at *
            obtain ⟨intermediate, firstResult⟩ := firstOutput
            change intermediate.clock ≤ state.clock at bound
            cases firstResult with
            | err error => simp at run
            | val heads =>
              generalize tailRun : evaluate env intermediate (second :: tail) = tailOutput at run
              obtain ⟨last, tailResult⟩ := tailOutput
              cases tailResult with
              | err error => simp at run
              | val tailValues =>
                simp at run
                rcases run with ⟨rfl, rfl⟩
                have tailLength := exprIH env intermediate last (second :: tail) tailValues (by omega)
                  (by simp only [expsWeight] at measure ⊢; omega) tailRun
                simpa using congrArg Nat.succ tailLength
          | nil =>
            cases first with
            | lit tra lit => simp [evaluate] at run; rcases run with ⟨_, rfl⟩; rfl
            | varLocal tra name =>
              cases lookup : env.v.lookup name <;> simp [evaluate, lookup] at run
              rcases run with ⟨_, rfl⟩; rfl
            | fn functionName argumentName body => simp [evaluate] at run; rcases run with ⟨_, rfl⟩; rfl
            | raise tra body =>
              rw [evaluate] at run
              generalize bodyEval : evaluate env state [body] = bodyOutput at run
              obtain ⟨bodyState, bodyResult⟩ := bodyOutput
              cases bodyResult <;> simp at run
            | con tra constructor args =>
              rw [evaluate] at run
              generalize argsEval : evaluate env state args.reverse = argsOutput at run
              obtain ⟨argsState, argsResult⟩ := argsOutput
              cases argsResult <;> simp at run
              rcases run with ⟨_, rfl⟩
              rfl
            | letrec name funs body =>
              rw [evaluate] at run
              split at run
              · have length := exprIH _ state next [body] values (by omega)
                  (by simp only [expsWeight, expWeight] at measure ⊢; omega) run
                simpa using length
              · simp at run
            | let_ tra name first body =>
              have bound := fixClock_clock_le state (evaluate env state [first])
              rw [evaluate] at run
              generalize firstEval : fixClock state (evaluate env state [first]) = firstOutput at run bound
              obtain ⟨intermediate, firstResult⟩ := firstOutput
              change intermediate.clock ≤ state.clock at bound
              cases firstResult with
              | err error => simp at run
              | val value =>
                simp only at run
                have length := exprIH _ intermediate next [body] values (by omega)
                  (by simp only [expsWeight, expWeight] at measure ⊢; omega) run
                simpa using length
            | if_ tra cond yes no =>
              have bound := fixClock_clock_le state (evaluate env state [cond])
              rw [evaluate] at run
              generalize condEval : fixClock state (evaluate env state [cond]) = condOutput at run bound
              obtain ⟨intermediate, condResult⟩ := condOutput
              change intermediate.clock ≤ state.clock at bound
              cases condResult with
              | err error => simp at run
              | val resultValues =>
                simp only at run
                split at run
                · simp at run
                · rename_i branch selected
                  have choice := doIf_selected _ yes no branch selected
                  rcases choice with yesEq | noEq
                  · rw [yesEq] at run
                    have length := exprIH env intermediate next [yes] values (by omega)
                      (by simp only [expsWeight, expWeight] at measure ⊢; omega) run
                    simpa using length
                  · rw [noEq] at run
                    have length := exprIH env intermediate next [no] values (by omega)
                      (by simp only [expsWeight, expWeight] at measure ⊢; omega) run
                    simpa using length
            | mat tra body rows =>
              have bound := fixClock_clock_le state (evaluate env state [body])
              rw [evaluate] at run
              generalize bodyEval : fixClock state (evaluate env state [body]) = bodyOutput at run bound
              obtain ⟨intermediate, bodyResult⟩ := bodyOutput
              change intermediate.clock ≤ state.clock at bound
              cases bodyResult with
              | err error => simp at run
              | val bodyValues =>
                simp only at run
                split at run
                · simp at run
                · rename_i bindings branch selected
                  have branchWeight := selectRow_weight rows intermediate _ bindExnV bindings branch selected
                  have length := exprIH _ intermediate next [branch] values (by omega)
                    (by simp only [expsWeight, expWeight] at measure ⊢; omega) run
                  simpa using length
            | handle tra body rows =>
              have bound := fixClock_clock_le state (evaluate env state [body])
              rw [evaluate] at run
              generalize bodyEval : evaluate env state [body] = bodyOutput at run bound
              obtain ⟨bodyState, bodyResult⟩ := bodyOutput
              simp only [fixClock] at run bound
              cases bodyResult with
              | val bodyValues =>
                simp at run
                rcases run with ⟨_, rfl⟩
                have length := exprIH env state bodyState [body] bodyValues (by omega)
                  (by simp only [expsWeight, expWeight] at measure ⊢; omega) bodyEval
                simpa using length
              | err error =>
                cases error with
                | abort error => simp at run
                | raise value =>
                  simp only at run
                  split at run
                  · simp at run
                  · rename_i bindings branch selected
                    have branchWeight := selectRow_weight rows _ value value bindings branch selected
                    have length := exprIH _ _ next [branch] values
                      (by simpa using Nat.le_trans (Nat.min_le_left state.clock bodyState.clock) (Nat.le_of_eq stateClock))
                      (by simp only [expsWeight, expWeight] at measure ⊢; omega) run
                    simpa using length
            | app tra op args =>
              have bound := fixClock_clock_le state (evaluate env state args.reverse)
              rw [evaluate] at run
              generalize argsEval : fixClock state (evaluate env state args.reverse) = argsOutput at run bound
              obtain ⟨intermediate, argsResult⟩ := argsOutput
              change intermediate.clock ≤ state.clock at bound
              cases argsResult with
              | err error => simp at run
              | val argValues =>
                simp only at run
                cases op with
                | src sourceOp =>
                  cases sourceOp <;> try simp only at run
                  all_goals try (have length := applyResult_length intermediate next _ _ values run; simpa using length)
                  case opapp =>
                    cases call : doOpApp argValues.reverse with
                    | none => simp [call] at run
                    | some pair =>
                      obtain ⟨newEnv, body⟩ := pair
                      by_cases zero : intermediate.clock = 0
                      · simp [call, zero] at run
                      · simp [call, zero] at run
                        have decrease : (decClock intermediate).clock < clock := by
                          simp only [decClock]
                          omega
                        have length := smallerExpr newEnv (decClock intermediate) next body values decrease run
                        simpa using length
                  case eval =>
                    cases decoded : doEval argValues.reverse intermediate.evalConfig with
                    | none => simp [decoded] at run
                    | some payload =>
                      obtain ⟨decs, config, returnValue⟩ := payload
                      by_cases zero : intermediate.clock = 0
                      · simp [decoded, zero] at run
                      · generalize decRun : evaluateDecs (decClock { intermediate with evalConfig := config }) decs = decOutput at run
                        obtain ⟨last, decResult⟩ := decOutput
                        cases decResult <;> simp [decoded, zero, decRun] at run
                        rcases run with ⟨_, rfl⟩
                        rfl
                  case thunkOp thunk =>
                    cases thunk with
                    | allocThunk mode => simpa using applyResult_length intermediate next _ _ values run
                    | updateThunk mode => simpa using applyResult_length intermediate next _ _ values run
                    | forceThunk =>
                      cases thunk : destThunk argValues intermediate.refs with
                      | badRef => simp [thunk] at run
                      | notThunk => simp [thunk] at run
                      | isThunk mode value =>
                        cases mode with
                        | evaluated =>
                          simp [thunk] at run
                          rcases run with ⟨_, rfl⟩
                          rfl
                        | notEvaluated =>
                          let name := Flapjack.Basis.Pure.MlString.ofString "f"
                          let body := appUnit (.varLocal .none name)
                          generalize bodyEval : evaluate ⟨[(name, value)]⟩ intermediate [body] = bodyOutput at run
                          obtain ⟨bodyState, bodyResult⟩ := bodyOutput
                          cases bodyResult with
                          | err error => simp [thunk, name, body, bodyEval] at run
                          | val bodyValues =>
                            cases updated : updateThunk argValues bodyState.refs bodyValues with
                            | none => simp [thunk, name, body, bodyEval, updated] at run
                            | some refs =>
                              simp [thunk, name, body, bodyEval, updated] at run
                              rcases run with ⟨_, rfl⟩
                              have forceWeight := appUnit_force_weight tra args
                              have length := exprIH ⟨[(name, value)]⟩ intermediate bodyState [body] bodyValues
                                (by omega)
                                (by simp only [expsWeight, expWeight] at measure ⊢
                                    simp only [body, name] at *
                                    simp only [expWeight] at forceWeight
                                    omega) bodyEval
                              simpa using length
                | globalVarAlloc n => simpa using applyResult_length intermediate next _ _ values run
                | globalVarInit n => simpa using applyResult_length intermediate next _ _ values run
                | globalVarLookup n => simpa using applyResult_length intermediate next _ _ values run
                | tagLenEq n l => simpa using applyResult_length intermediate next _ _ values run
                | lenEq l => simpa using applyResult_length intermediate next _ _ values run
                | el n => simpa using applyResult_length intermediate next _ _ values run
                | id => simpa using applyResult_length intermediate next _ _ values run
  intro env state next expressions values run
  exact allRanks state.clock (expsWeight expressions) env state next expressions values rfl rfl run

/-- Successful singleton evaluation returns exactly one value. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_sing"]
theorem evaluate_sing {C F : Type} (env : Environment Value) (state next : State C F)
    (expression : FlatLang.Exp) (values : List Value)
    (run : evaluate env state [expression] = (next, .val values)) :
    ∃ value, values = [value] := by
  have length := evaluate_length env state next [expression] values run
  cases values with
  | nil => simp at length
  | cons value rest =>
    cases rest with
    | nil => exact ⟨value, rfl⟩
    | cons other rest => simp at length

end Flapjack.Compiler.Backend.FlatProps
