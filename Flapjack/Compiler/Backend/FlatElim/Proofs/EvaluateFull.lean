module

public import Flapjack.Compiler.Backend.FlatElim.Proofs.EvaluateInduction
public import Flapjack.Misc.ClockWeightInduction
public import Flapjack.Compiler.Backend.Semantics.FlatSem.MeasureMembers

@[expose] public section

/-! Nested-induction assembly of the flat evaluation simulation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.FlatSem

/-- Induction motive for the full flat evaluation simulation; this is a
Flapjack proof helper with no separate HOL theorem. -/
private theorem evaluationSimulation_all {C F : Type} (expressions : List FlatLang.Exp) :
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
  | nil =>
    intro next result reachable target run _lookups related _envClosed _envSafe _exprSafe _notTypeError
    simp [FlatSem.evaluate] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨target, by simp [FlatSem.evaluate], related, ?_, ?_⟩
    · simp [findPrimitiveResultGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain]
    · simp [Flapjack.Compiler.Backend.FlatProps.resultValues, valuesNoEval]
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
      | lit tra lit =>
        intro next result reachable target run _lookups related _envClosed _envSafe _exprSafe _notTypeError
        simp [FlatSem.evaluate] at run
        rcases run with ⟨rfl, rfl⟩
        have resultSafe := primitiveResult_value_invariants reachable (.litv lit)
          (by simp [findValueGlobals, globalsWithin, sptMem, sptDomain]) (by simp [valueHasEval])
        exact ⟨target, by simp [FlatSem.evaluate], related, resultSafe.1, resultSafe.2⟩
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
            intro next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
            have impossible := expressionsSafe (.app tra (.src .eval) args) (by simp)
            simp [hasEval] at impossible
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

/-- Full flat evaluation simulation. The evaluator and carriers remain
the statement has been reviewed against the pinned HOL source; the evaluator
and carrier renderings are recorded in docs/HOL-THEOREM-MAP.json. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_keep_flat_state_rel_eq_lemma"]
theorem evaluate_keep_flatStateRel {C F : Type} (env : Environment FlatSem.Value)
    (state : State C F) (expressions : List FlatLang.Exp) (next : State C F)
    (result : Result (List FlatSem.Value) FlatSem.Value) (reachable : NumSet)
    (target : State C F)
    (premises : FlatSem.evaluate env state expressions = (next, result) ∧
      globalsWithin (findGlobalsList destGlobalVarLookup expressions) reachable ∧
      flatStateRel reachable state target ∧ globalsWithin (findEnvGlobals env) reachable ∧
      bindingsNoEval env.v ∧ expressionsNoEval expressions ∧
      result ≠ .err (.abort .typeError)) :
    ∃ targetNext, FlatSem.evaluate env target expressions = (targetNext, result) ∧
      flatStateRel reachable next targetNext ∧ globalsWithin (findPrimitiveResultGlobals result) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues result) := by
  obtain ⟨run, lookups, related, envClosed, envSafe, exprSafe, notTypeError⟩ := premises
  exact evaluationSimulation_all expressions env state next result reachable target
    run lookups related envClosed envSafe exprSafe notTypeError

end Flapjack.Compiler.Backend.FlatElim
