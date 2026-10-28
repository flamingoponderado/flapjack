import Flapjack.Compiler.Backend.FlatElim.Proofs.PureControl

/-! Full pure-expression simulation for flat elimination. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.FlatSem

/-- Evaluation of pure, Eval-free expressions that initialize no reachable
globals leaves the result state related to the unchanged target and returns
only Eval-free values. The evaluator and carriers remain pending HOL review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_flat_state_rel_lemma"]
theorem evaluate_pure_flatStateRel {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state : FlatSem.State C F) (expressions : List FlatLang.Exp) :
    pureEvaluationSimulationAt env state expressions := by
  have allWeights : ∀ weight : Nat, ∀ (env : FlatSem.Environment FlatSem.Value)
      (state : FlatSem.State C F) (expressions : List FlatLang.Exp),
      expsWeight expressions = weight → pureEvaluationSimulationAt env state expressions := by
    intro weight
    induction weight using Nat.strongRecOn with
    | ind weight ih =>
      intro env state expressions measure
      have exprIH : ∀ (newEnv : FlatSem.Environment FlatSem.Value) (newState : FlatSem.State C F)
          (es : List FlatLang.Exp), expsWeight es < weight → pureEvaluationSimulationAt newEnv newState es := by
        intro newEnv newState es smaller
        exact ih (expsWeight es) smaller newEnv newState es rfl
      cases expressions with
      | nil => exact pureEvaluation_empty env state
      | cons first rest =>
        cases rest with
        | cons second tail =>
          apply pureEvaluation_list
          · apply exprIH env state [first]
            simp only [expsWeight] at measure ⊢
            omega
          · intro next _
            apply exprIH env next (second :: tail)
            simp only [expsWeight] at measure ⊢
            omega
        | nil =>
          cases first with
          | lit tra literal => exact pureEvaluation_lit env state tra literal
          | varLocal tra name => exact pureEvaluation_var env state tra name
          | fn name argument body => exact pureEvaluation_fn env state name argument body
          | raise tra body =>
            intro next result reachable target run pure
            have impossible := pure (.raise tra body) (by simp)
            simp [isPure] at impossible
          | con tra constructor args =>
            apply pureEvaluation_con
            apply exprIH env state args.reverse
            rw [expsWeight_reverse]
            simp only [expsWeight, expWeight] at measure
            omega
          | letrec name funs body =>
            apply pureEvaluation_letrec
            intro newEnv
            apply exprIH newEnv state [body]
            simp only [expsWeight, expWeight] at measure ⊢
            omega
          | let_ tra name first body =>
            apply pureEvaluation_let
            · apply exprIH env state [first]
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            · intro newEnv next _
              apply exprIH newEnv next [body]
              simp only [expsWeight, expWeight] at measure ⊢
              omega
          | if_ tra cond yes no =>
            apply pureEvaluation_if
            · apply exprIH env state [cond]
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            · intro next _
              apply exprIH env next [yes]
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            · intro next _
              apply exprIH env next [no]
              simp only [expsWeight, expWeight] at measure ⊢
              omega
          | handle tra body rows =>
            apply pureEvaluation_handle
            apply exprIH env state [body]
            simp only [expsWeight, expWeight] at measure ⊢
            omega
          | mat tra body rows =>
            apply pureEvaluation_mat
            · apply exprIH env state [body]
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            · intro pattern branch member newEnv next _
              apply exprIH newEnv next [branch]
              have bound := rowsWeight_member rows pattern branch member
              simp only [expsWeight, expWeight] at measure ⊢
              omega
          | app tra op args =>
            cases op
            case globalVarInit index =>
              apply pureEvaluation_globalInit
              apply exprIH env state args.reverse
              rw [expsWeight_reverse]
              simp only [expsWeight, expWeight] at measure
              omega
            all_goals
              intro next result reachable target run pure
              have impossible := pure _ (List.mem_singleton_self _)
              simp [isPure] at impossible
  exact allWeights (expsWeight expressions) env state expressions rfl

end Flapjack.Compiler.Backend.FlatElim
