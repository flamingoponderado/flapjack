import Flapjack.Compiler.Backend.FlatPattern.Proofs.HandleBranch
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateLength

/-! Composition of the match-expression cases. The evaluator's HOL
correspondence remains pending review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- The successful evaluation of an expression yields exactly one value. -/
def SingletonSuccess {C F : Type} (expression : FlatLang.Exp) : Prop :=
  ∀ (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F) (values : List FlatSem.Value),
    FlatSem.evaluate env state [expression] = (next, .val values) → ∃ value, values = [value]

/-- An error in a match scrutinee propagates through the source match. -/
theorem evaluate_mat_error {C F : Type} (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F)
    (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (run : FlatSem.evaluate env state [scrutinee] = (next, .err error)) :
    FlatSem.evaluate env state [.mat trace scrutinee rows] =
      ({ next with clock := min state.clock next.clock }, .err error) := by
  simp [FlatSem.evaluate, run, FlatSem.fixClock]

/-- An error in the generated let initializer propagates without dispatch. -/
theorem evaluate_let_error {C F : Type} (trace : BackendCommon.Tra) (name : VarN)
    (first body : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (run : FlatSem.evaluate env state [first] = (next, .err error)) :
    FlatSem.evaluate env state [.let_ trace (some name) first body] =
      ({ next with clock := min state.clock next.clock }, .err error) := by
  simp [FlatSem.evaluate, run, FlatSem.fixClock]

/-- A type-failing source row makes the match expression type-fail. -/
theorem evaluate_mat_rowTypeError {C F : Type} (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F) (value : FlatSem.Value)
    (run : FlatSem.evaluate env state [scrutinee] = (next, .val [value]))
    (selected : FlatSem.pmatchRows rows { next with clock := min state.clock next.clock } value = .typeError) :
    FlatSem.evaluate env state [.mat trace scrutinee rows] =
      ({ next with clock := min state.clock next.clock }, .err (.abort .typeError)) := by
  simp only [FlatSem.evaluate, run, FlatSem.fixClock]
  split <;> simp_all [FlatSem.selectRow]

/-- Duplicate variables in a selected match row make the expression type-fail. -/
theorem evaluate_mat_duplicate {C F : Type} (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F) (value : FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (run : FlatSem.evaluate env state [scrutinee] = (next, .val [value]))
    (selected : FlatSem.pmatchRows rows { next with clock := min state.clock next.clock } value =
      .match (bindings, pattern, body)) (duplicate : ¬(FlatLang.patBindings pattern).Nodup) :
    FlatSem.evaluate env state [.mat trace scrutinee rows] =
      ({ next with clock := min state.clock next.clock }, .err (.abort .typeError)) := by
  simp only [FlatSem.evaluate, run, FlatSem.fixClock]
  split <;> simp_all [FlatSem.selectRow]

/-- Compilation's generated-name bound for a match expression. -/
theorem compileExp_mat_bound (cfg : Config) (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    (compileExp cfg (.mat trace scrutinee rows)).1 =
      max (compileExp cfg scrutinee).1 (compileMatch cfg rows).1 + 2 := by
  cases first : compileExp cfg scrutinee with
  | mk bound rest =>
    cases rest with
    | mk flag expression =>
      cases matchResult : compileMatch cfg rows with
      | mk rowBound rest =>
        cases rest with
        | mk rowFlag compiledRows => simp [compileExp, first, matchResult]

/-- Match-expression simulation given the scrutinee and branch induction
hypotheses and singleton-result preservation for the scrutinee. -/
theorem compile_mat_simulation_of_singleton {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (singleton : SingletonSuccess (C := C) (F := F) scrutinee)
    (scrutineeIH : ExpressionSimulation (C := C) (F := F) cfg stateCfg scrutinee)
    (bodiesIH : ∀ pattern body, (pattern, body) ∈ rows → ExpressionSimulation (C := C) (F := F) cfg stateCfg body) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.mat trace scrutinee rows) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states bound safe
  have generatedBound : max (compileExp cfg scrutinee).1 (compileMatch cfg rows).1 + 2 < n := by
    simpa [compileExp_mat_bound] using bound
  have scrutineeBound : (compileExp cfg scrutinee).1 < n := by omega
  cases scrutineeRun : FlatSem.evaluate sourceEnv source [scrutinee] with
  | mk sourceNext scrutineeResult =>
    have scrutineeSafe : scrutineeResult ≠ .err (.abort .typeError) := by
      intro bad
      subst scrutineeResult
      have run := evaluate_mat_error trace scrutinee rows sourceEnv source sourceNext (.abort .typeError) scrutineeRun
      rw [sourceEval] at run
      exact safe (congrArg Prod.snd run)
    obtain ⟨targetNext, targetResult, targetRun, nextStates, related⟩ := scrutineeIH
      sourceEnv targetEnv source target sourceNext scrutineeResult n scrutineeRun envs states scrutineeBound scrutineeSafe
    cases related with
    | error errorsRel =>
      rename_i sourceError targetError
      have sourceRun := evaluate_mat_error trace scrutinee rows sourceEnv source sourceNext _ scrutineeRun
      have targetRun' : FlatSem.evaluate targetEnv target [(compileExp cfg (.mat trace scrutinee rows)).2.2] =
          ({ targetNext with clock := min target.clock targetNext.clock }, .err targetError) := by
        rw [compileExp_mat_body]
        apply evaluate_let_error
        exact targetRun
      have equal := sourceEval.symm.trans sourceRun
      cases equal
      exact ⟨_, _, targetRun', stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, .error errorsRel⟩
    | values valuesRel =>
      rename_i values values'
      obtain ⟨value, valuesEq⟩ := singleton sourceEnv source sourceNext values scrutineeRun
      subst values
      cases valuesRel with
      | cons valueRel tailRel =>
        cases tailRel
        rename_i value'
        let sourceFixed := { sourceNext with clock := min source.clock sourceNext.clock }
        let targetFixed := { targetNext with clock := min target.clock targetNext.clock }
        have fixedStates : StateRel stateCfg sourceFixed targetFixed :=
          stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates
        cases rowResult : FlatSem.pmatchRows rows sourceFixed value with
        | typeError =>
          have run := evaluate_mat_rowTypeError trace scrutinee rows sourceEnv source sourceNext value scrutineeRun rowResult
          rw [sourceEval] at run
          exact (safe (congrArg Prod.snd run)).elim
        | noMatch =>
          obtain ⟨sourceFinal', targetFinal, sourceResult', targetResult', sourceRun, targetRun', finalRel, resultRel⟩ :=
            compile_mat_noMatch_forward cfg stateCfg trace scrutinee rows source sourceNext target targetNext
              sourceEnv targetEnv value value' scrutineeRun targetRun fixedStates valueRel rowResult
          have equal := sourceEval.symm.trans sourceRun
          cases equal
          exact ⟨targetFinal, targetResult', targetRun', finalRel, resultRel⟩
        | «match» selected =>
          rcases selected with ⟨bindings, pattern, body⟩
          have distinct : (FlatLang.patBindings pattern).Nodup := by
            by_cases distinct : (FlatLang.patBindings pattern).Nodup
            · exact distinct
            · have run := evaluate_mat_duplicate trace scrutinee rows sourceEnv source sourceNext value
                bindings pattern body scrutineeRun rowResult distinct
              rw [sourceEval] at run
              exact (safe (congrArg Prod.snd run)).elim
          have sourceBody : FlatSem.evaluate { sourceEnv with v := bindings ++ sourceEnv.v } sourceFixed [body] =
              (sourceFinal, sourceResult) := by
            have run := evaluate_mat_selected trace scrutinee rows sourceEnv source sourceNext value
              bindings pattern body scrutineeRun rowResult distinct
            exact run.symm.trans sourceEval
          have member := pmatchRows_match_mem sourceFixed value rows bindings pattern body rowResult
          have bodySim := bodiesIH pattern body member
          let generated := max (compileExp cfg scrutinee).1 (compileMatch cfg rows).1 + 2
          have bodyBound : (compileExp cfg body).1 < generated - 1 := by
            have bodyLe := (compileMatch_member_bound cfg rows pattern body member).1
            dsimp [generated]
            omega
          have bodyIH : ∀ extEnv,
              EnvRel (generated - 1) { sourceEnv with v := bindings ++ sourceEnv.v } extEnv →
              FlatSem.evaluate { sourceEnv with v := bindings ++ sourceEnv.v } sourceFixed [body] = (sourceFinal, sourceResult) →
              ∃ targetFinal targetResult,
                FlatSem.evaluate extEnv targetFixed [(compileExp cfg body).2.2] = (targetFinal, targetResult) ∧
                StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult := by
            intro extEnv envRel evaluated
            exact bodySim _ _ _ _ _ _ _ evaluated envRel fixedStates bodyBound safe
          obtain ⟨_, targetFinal, targetResult', targetRun', finalRel, resultRel⟩ :=
            compile_mat_selected_forward cfg stateCfg trace scrutinee rows source sourceNext target targetNext sourceFinal
              sourceEnv targetEnv value value' bindings pattern body sourceResult n scrutineeRun targetRun fixedStates
              valueRel envs (by dsimp [generated] at *; omega) rowResult distinct sourceBody bodyIH
          exact ⟨targetFinal, targetResult', targetRun', finalRel, resultRel⟩

/-- Every scrutinee has the singleton-result property in the current evaluator. -/
theorem singletonSuccess {C F : Type} (expression : FlatLang.Exp) : SingletonSuccess (C := C) (F := F) expression := by
  intro env state next values run
  have length := FlatSem.evaluate_singleton_length env state next expression values run
  cases values with
  | nil => simp at length
  | cons value rest =>
    cases rest with
    | nil => exact ⟨value, rfl⟩
    | cons first rest => simp at length

/-- Match expressions satisfy the forward simulation when their scrutinee and
row bodies satisfy their induction hypotheses. The evaluator and relations
remain pending HOL correspondence review. -/
theorem compile_mat_simulation {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (scrutinee : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (scrutineeIH : ExpressionSimulation (C := C) (F := F) cfg stateCfg scrutinee)
    (bodiesIH : ∀ pattern body, (pattern, body) ∈ rows → ExpressionSimulation (C := C) (F := F) cfg stateCfg body) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.mat trace scrutinee rows) :=
  compile_mat_simulation_of_singleton cfg stateCfg trace scrutinee rows (singletonSuccess scrutinee) scrutineeIH bodiesIH

end Flapjack.Compiler.Backend.FlatPattern
