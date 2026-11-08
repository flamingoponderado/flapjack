import Flapjack.Compiler.Backend.FlatElim.Proofs.EvaluateInduction
import Flapjack.Misc.ClockWeightInduction

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
  intro env source
  refine clockWeightInduction (α := List FlatLang.Exp) (σ := State C F) (·.clock) expsWeight
    (motive := fun expressions state => ∀ env', evaluationSimulationAt env' state expressions) ?_
    expressions source env
  intro expressions state exprIH₀ smaller₀
  have exprIH := fun (env' : Environment FlatSem.Value) (s : State C F) (es : List FlatLang.Exp)
      h1 h2 => exprIH₀ es s h1 h2 env'
  have smallerExpr := fun (env' : Environment FlatSem.Value) (s : State C F) (e : FlatLang.Exp)
      h => smaller₀ [e] s h env'
  intro env
  cases expressions with
  | nil => exact fun next result reachable target => evaluate_keep_flatStateRel_empty env state next
             target result reachable
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply evaluate_list_simulation_step
      · apply exprIH env state [first] (by omega)
        simp only [expsWeight] at ⊢
        omega
      · intro next nextBound
        apply exprIH env next (second :: tail) (by omega)
        simp only [expsWeight] at ⊢
        omega
    | nil =>
      cases first with
      | lit tra lit => exact fun next result reachable target => evaluate_keep_flatStateRel_lit env
                         state next target result reachable tra lit
      | varLocal tra name =>
        exact fun next result reachable target =>
          evaluate_keep_flatStateRel_var env state next target result reachable tra name
      | fn functionName argumentName body =>
        exact fun next result reachable target =>
          evaluate_keep_flatStateRel_fn env state next target result reachable functionName
            argumentName body
      | raise tra body =>
        apply evaluate_raise_simulation_step
        apply exprIH env state [body] (by omega)
        simp only [expsWeight, expWeight] at ⊢
        omega
      | con tra constructor args =>
        apply evaluate_con_simulation_step
        apply exprIH env state args.reverse (by omega)
        rw [expsWeight_reverse]
        simp only [expsWeight, expWeight] at ⊢
        omega
      | letrec name funs body =>
        apply evaluate_letrec_simulation_step
        intro newEnv
        apply exprIH newEnv state [body] (by omega)
        simp only [expsWeight, expWeight] at ⊢
        omega
      | let_ tra name first body =>
        apply evaluate_let_simulation_step
        · apply exprIH env state [first] (by omega)
          simp only [expsWeight, expWeight] at ⊢
          omega
        · intro newEnv next nextBound
          apply exprIH newEnv next [body] (by omega)
          simp only [expsWeight, expWeight] at ⊢
          omega
      | if_ tra cond yes no =>
        apply evaluate_if_simulation_step
        · apply exprIH env state [cond] (by omega)
          simp only [expsWeight, expWeight] at ⊢
          omega
        · intro next nextBound
          apply exprIH env next [yes] (by omega)
          simp only [expsWeight, expWeight] at ⊢
          omega
        · intro next nextBound
          apply exprIH env next [no] (by omega)
          simp only [expsWeight, expWeight] at ⊢
          omega
      | mat tra body rows =>
        apply evaluate_mat_simulation_step
        · apply exprIH env state [body] (by omega)
          simp only [expsWeight, expWeight] at ⊢
          omega
        · intro pattern branch member newEnv next nextBound
          apply exprIH newEnv next [branch] (by omega)
          have bound := rowsWeight_member rows pattern branch member
          simp only [expsWeight, expWeight] at ⊢
          omega
      | handle tra body rows =>
        apply evaluate_handle_simulation_step
        · apply exprIH env state [body] (by omega)
          simp only [expsWeight, expWeight] at ⊢
          omega
        · intro pattern branch member newEnv next nextBound
          apply exprIH newEnv next [branch] (by omega)
          have bound := rowsWeight_member rows pattern branch member
          simp only [expsWeight, expWeight] at ⊢
          omega
      | app tra op args =>
        have argsIH : evaluationSimulationAt env state args.reverse := by
          apply exprIH env state args.reverse (by omega)
          rw [expsWeight_reverse]
          simp only [expsWeight, expWeight] at ⊢
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
              simp only [expsWeight, expWeight] at ⊢
              simp only [expWeight] at forceWeight
              omega
            · exact evaluate_ordinary_simulation_step env state tra op args ⟨call, eval, force⟩
                argsIH

end Flapjack.Compiler.Backend.FlatElim
