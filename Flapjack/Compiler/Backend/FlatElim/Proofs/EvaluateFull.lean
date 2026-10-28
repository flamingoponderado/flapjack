import Flapjack.Compiler.Backend.FlatElim.Proofs.EvaluateInduction

/-! Nested-induction assembly of the flat evaluation simulation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.FlatSem

/-- Every member body has less weight than its enclosing pattern-row list. -/
theorem rowsWeight_member (rows : List (FlatLang.Pat × FlatLang.Exp))
    (pattern : FlatLang.Pat) (body : FlatLang.Exp) (member : (pattern, body) ∈ rows) :
    expWeight body < rowsWeight rows := by
  induction rows with
  | nil => simp at member
  | cons row rest ih =>
    obtain ⟨p, e⟩ := row
    rcases List.mem_cons.mp member with same | member
    · cases same
      simp [rowsWeight]
      omega
    · have bound := ih member
      simp [rowsWeight]
      omega

/-- Full flat evaluation simulation. The evaluator and carriers remain
pending complete HOL correspondence review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_keep_flat_state_rel_eq_lemma"]
theorem evaluate_keep_flatStateRel {C F : Type} (expressions : List FlatLang.Exp) :
    evaluationSimulation (C := C) (F := F) expressions := by
  have allRanks : ∀ clock weight : Nat,
      ∀ (env : Environment FlatSem.Value) (state : State C F) (expressions : List FlatLang.Exp),
        state.clock = clock → expsWeight expressions = weight → evaluationSimulationAt env state expressions := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (env : Environment FlatSem.Value) (state : State C F) (expressions : List FlatLang.Exp),
            state.clock ≤ clock → expsWeight expressions < weight → evaluationSimulationAt env state expressions := by
          intro env state expressions clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact (clockIH state.clock clockLt) (expsWeight expressions) env state expressions rfl rfl
          · exact (weightIH (expsWeight expressions) weightLt) env state expressions clockEq rfl
        have smallerExpr : ∀ (env : Environment FlatSem.Value) (state : State C F) (body : FlatLang.Exp),
            state.clock < clock → evaluationSimulationAt env state [body] := by
          intro env state body clockLt
          exact (clockIH state.clock clockLt) (expsWeight [body]) env state [body] rfl rfl
        intro env state expressions stateClock measure
        cases expressions with
        | nil => exact fun next result reachable target => evaluate_keep_flatStateRel_empty env state next target result reachable
        | cons first rest =>
          cases rest with
          | cons second tail =>
            apply evaluate_list_simulation_step
            · apply exprIH env state [first] (by omega)
              simp only [expsWeight] at measure ⊢
              omega
            · intro next nextBound
              apply exprIH env next (second :: tail) (by omega)
              simp only [expsWeight] at measure ⊢
              omega
          | nil =>
            cases first with
            | lit tra lit => exact fun next result reachable target => evaluate_keep_flatStateRel_lit env state next target result reachable tra lit
            | varLocal tra name => exact fun next result reachable target => evaluate_keep_flatStateRel_var env state next target result reachable tra name
            | fn functionName argumentName body => exact fun next result reachable target => evaluate_keep_flatStateRel_fn env state next target result reachable functionName argumentName body
            | raise tra body =>
              apply evaluate_raise_simulation_step
              apply exprIH env state [body] (by omega)
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | con tra constructor args =>
              apply evaluate_con_simulation_step
              apply exprIH env state args.reverse (by omega)
              rw [expsWeight_reverse]
              simp only [expsWeight, expWeight] at measure
              omega
            | letrec name funs body =>
              apply evaluate_letrec_simulation_step
              intro newEnv
              apply exprIH newEnv state [body] (by omega)
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | let_ tra name first body =>
              apply evaluate_let_simulation_step
              · apply exprIH env state [first] (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro newEnv next nextBound
                apply exprIH newEnv next [body] (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
            | if_ tra cond yes no =>
              apply evaluate_if_simulation_step
              · apply exprIH env state [cond] (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro next nextBound
                apply exprIH env next [yes] (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro next nextBound
                apply exprIH env next [no] (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
            | mat tra body rows =>
              apply evaluate_mat_simulation_step
              · apply exprIH env state [body] (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro pattern branch member newEnv next nextBound
                apply exprIH newEnv next [branch] (by omega)
                have bound := rowsWeight_member rows pattern branch member
                simp only [expsWeight, expWeight] at measure ⊢
                omega
            | handle tra body rows =>
              apply evaluate_handle_simulation_step
              · apply exprIH env state [body] (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro pattern branch member newEnv next nextBound
                apply exprIH newEnv next [branch] (by omega)
                have bound := rowsWeight_member rows pattern branch member
                simp only [expsWeight, expWeight] at measure ⊢
                omega
            | app tra op args =>
              have argsIH : evaluationSimulationAt env state args.reverse := by
                apply exprIH env state args.reverse (by omega)
                rw [expsWeight_reverse]
                simp only [expsWeight, expWeight] at measure
                omega
              by_cases call : op = .src .opapp
              · subst op
                apply evaluate_call_simulation_step env state tra args argsIH
                intro newEnv next body nextLt
                exact smallerExpr newEnv next body (by omega)
              · by_cases eval : op = .src .eval
                · subst op
                  exact evaluate_keep_flatStateRel_appEval tra args env state
                · by_cases force : op = .src (.thunkOp .forceThunk)
                  · subst op
                    apply evaluate_force_simulation_step env state tra args argsIH
                    intro next value nextBound
                    apply exprIH _ next _ (by omega)
                    have forceWeight := appUnit_force_weight tra args
                    simp only [expsWeight, expWeight] at measure ⊢
                    simp only [expWeight] at forceWeight
                    omega
                  · exact evaluate_ordinary_simulation_step env state tra op args ⟨call, eval, force⟩ argsIH
  intro env state
  exact allRanks state.clock (expsWeight expressions) env state expressions rfl rfl

end Flapjack.Compiler.Backend.FlatElim
