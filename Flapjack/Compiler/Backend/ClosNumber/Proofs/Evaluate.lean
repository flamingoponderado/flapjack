module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.EvaluateInstall

@[expose] public section

/-! Mutual evaluator simulation for closure numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Indirect application simulation at one source state. -/
def AppSimulationAt {C F : Type} (source : State (Nat × C) F) : Prop :=
  ∀ (function nextFunction : Value) (args nextArgs : List Value) (target : State C F)
    (result : Result (List Value) Value) (sourceNext : State (Nat × C) F),
    evaluateApp none function args source = (result, sourceNext) →
    result ≠ .err (.abort .typeError) → ValueRel source.maxApp function nextFunction →
    List.Forall₂ (ValueRel source.maxApp) args nextArgs → StateRel source target →
    ∃ targetResult targetNext,
      evaluateApp none nextFunction nextArgs target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext

/-- Mutual simulation factored through local Lean predicates. This helper has
no separate HOL declaration; the source-shaped theorem follows below. -/
theorem evaluate_simulation {C F : Type} :
    (∀ expressions, EvalSimulation (C := C) (F := F) expressions) ∧
      AppSimulation (C := C) (F := F) := by
  have all : ∀ clock : Nat,
      (∀ source : State (Nat × C) F, source.clock = clock → AppSimulationAt source) ∧
      (∀ weight expressions (source : State (Nat × C) F),
        source.clock = clock → expsWeight expressions = weight → EvalSimulationAt source expressions) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ source : State (Nat × C) F, source.clock = clock → AppSimulationAt source := by
        intro source clockEq function nextFunction args nextArgs target result sourceNext run noType related argsRel states
        apply appSimulation_clock_step function nextFunction args nextArgs source target result sourceNext
          run noType related argsRel states
        · intro body state smaller
          exact (clockIH state.clock (by omega)).2 (expsWeight [body]) [body] state rfl rfl
        · intro function nextFunction args nextArgs state target result next smaller
          exact (clockIH state.clock (by omega)).1 state rfl function nextFunction args nextArgs target result next
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ expressions (state : State (Nat × C) F),
              state.clock ≤ clock → expsWeight expressions < weight → EvalSimulationAt state expressions := by
            intro expressions state clockLe weightLt
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions state rfl rfl
            · exact weightIH (expsWeight expressions) weightLt expressions state clockEq rfl
          have appBound : AppSimulationClockBelow (C := C) (F := F) (clock + 1) := by
            intro function nextFunction args nextArgs state target result next smaller
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ smaller) with clockLt | clockEq
            · exact (clockIH state.clock clockLt).1 state rfl function nextFunction args nextArgs target result next
            · exact appAll state clockEq function nextFunction args nextArgs target result next
          intro expressions source clockEq measure
          cases expressions with
          | nil => exact evalSimulation_at evaluate_nil source
          | cons first rest =>
            cases rest with
            | cons second tail =>
              apply evaluate_cons_step first second tail source
              · apply exprIH [first] source (by omega)
                simp only [expsWeight] at measure ⊢; omega
              · intro state bound
                apply exprIH (second :: tail) state (by omega)
                simp only [expsWeight] at measure ⊢; omega
            | nil =>
              cases first with
              | var trace index => exact evalSimulation_at (evaluate_var trace index) source
              | fn name location selected arity body =>
                exact evalSimulation_at (evaluate_fn name location selected arity body) source
              | raise trace body =>
                apply evaluate_raise_step trace body source
                apply exprIH [body] source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | tick trace body =>
                apply evaluate_tick_step trace body source
                apply exprIH [body] (decClock 1 source) (by simp [decClock]; omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | call trace ticks location args =>
                intro env nextEnv target result next start run noType safe envRel states
                apply evaluate_call_step trace ticks location args env nextEnv source target result next start
                  run noType safe envRel states
                apply exprIH args source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | «let» trace bindings body =>
                apply evaluate_let_step trace bindings body source
                · apply exprIH bindings source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [body] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | letrec names location selected functions body =>
                apply evaluate_letrec_step names location selected functions body source
                apply exprIH [body] source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | handle trace body handler =>
                apply evaluate_handle_step trace body handler source
                · apply exprIH [body] source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [handler] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | ifThenElse trace condition yes no =>
                apply evaluate_if_step trace condition yes no source
                · apply exprIH [condition] source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [yes] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro state bound
                  apply exprIH [no] state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | app trace location function args =>
                cases location with
                | some location => exact evalSimulation_at (evaluate_app_some trace location function args) source
                | none =>
                  intro env nextEnv target result next start run noType safe envRel states
                  apply evaluate_app_step trace function args env nextEnv source target result next start
                    run noType safe envRel states
                  · apply exprIH args source (by omega)
                    simp only [expsWeight, expWeight] at measure ⊢; omega
                  · intro state bound
                    apply exprIH [function] state (by omega)
                    simp only [expsWeight, expWeight] at measure ⊢; omega
                  · simpa [clockEq] using appBound
              | op trace op args =>
                have argsSmaller : expsWeight args < weight := by
                  have h := opWeight_gt trace op args
                  simp only [expsWeight] at measure
                  omega
                have argsIH := exprIH args source (by omega) argsSmaller
                have ordinary : ∀ op, op ≠ .install → op ≠ .thunkOp .forceThunk →
                    EvalSimulationAt source [.op trace op args] := by
                  intro op notInstall notForce env nextEnv target result next start run noType safe envRel states
                  exact evaluate_ordinaryOp_step trace op args notInstall notForce env nextEnv source target
                    result next start run noType safe envRel states argsIH (primitiveSimulation_ordinary op notInstall notForce)
                cases op with
                | install =>
                  intro env nextEnv target result next start run noType safe envRel states
                  apply evaluate_install_step trace args env nextEnv source target argsIH result next start
                    run noType safe envRel states
                  intro program state smaller
                  exact (clockIH state.clock (by omega)).2 (expsWeight program) program state rfl rfl
                | thunkOp operation =>
                  cases operation with
                  | forceThunk =>
                    intro env nextEnv target result next start run noType safe envRel states
                    apply evaluate_forceThunk_step trace args env nextEnv source target result next start
                      run noType safe envRel states argsIH
                    intro state bound
                    apply exprIH [appUnit (.var .none 0)] state (by omega)
                    have h := appUnit_var_weight
                    simp only [expsWeight, expWeight] at measure
                    simp only [appUnit, expsWeight, expWeight] at h ⊢
                    omega
                  | allocThunk mode => exact ordinary _ (by simp) (by simp)
                  | updateThunk mode => exact ordinary _ (by simp) (by simp)
                | label index => exact ordinary _ (by simp) (by simp)
                | ffi name => exact ordinary _ (by simp) (by simp)
                | intOp operation => exact ordinary _ (by simp) (by simp)
                | wordOp operation => exact ordinary _ (by simp) (by simp)
                | blockOp operation => exact ordinary _ (by simp) (by simp)
                | globOp operation => exact ordinary _ (by simp) (by simp)
                | memOp operation => exact ordinary _ (by simp) (by simp)
  constructor
  · intro expressions env nextEnv source target result next start run noType safe envRel states
    exact (all source.clock).2 (expsWeight expressions) expressions source rfl rfl
      env nextEnv target result next start run noType safe envRel states
  · intro function nextFunction args nextArgs source target result next run noType related argsRel states
    exact (all source.clock).1 source rfl function nextFunction args nextArgs target result next
      run noType related argsRel states

namespace EvaluatePort
/-- The closure state retains both finite maps through the canonical view. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EvaluatePort

/-- The mutual expression and indirect-application numbering simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "renumber_code_locs_correct"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_simulation_sourceShape {C F : Type} :
    (∀ (tmp : List ClosLang.Exp × List Value × State (Nat × C) F)
      (xs : List ClosLang.Exp) (env : List Value) (source : State (Nat × C) F)
      (nextEnv : List Value) (target : State C F) (result : Result (List Value) Value)
      (sourceNext : State (Nat × C) F) (start : Nat),
      tmp = (xs, env, source) ∧ evaluate xs env source = (result, sourceNext) ∧
        result ≠ .err (.abort .typeError) →
      ¬ ClosProps.containsAppSome source.maxApp xs ∧
        List.Forall₂ (ValueRel source.maxApp) env nextEnv ∧ StateRel source target →
      ∃ targetResult targetNext,
        evaluate (renumberList start xs).2 nextEnv target = (targetResult, targetNext) ∧
        ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext) ∧
    (∀ (location : Option Nat) (function : Value) (args : List Value)
      (source : State (Nat × C) F) (result : Result (List Value) Value)
      (sourceNext : State (Nat × C) F) (nextFunction : Value) (nextArgs : List Value)
      (target : State C F),
      evaluateApp location function args source = (result, sourceNext) ∧
        result ≠ .err (.abort .typeError) →
      ValueRel source.maxApp function nextFunction ∧ location = none ∧
        List.Forall₂ (ValueRel source.maxApp) args nextArgs ∧ StateRel source target →
      ∃ targetResult targetNext,
        evaluateApp location nextFunction nextArgs target = (targetResult, targetNext) ∧
        ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext) := by
  constructor
  · intro tmp xs env source nextEnv target result sourceNext start ⟨_, run, noType⟩ ⟨safe, envRel, states⟩
    exact evaluate_simulation.1 xs env nextEnv source target result sourceNext start run noType safe envRel states
  · intro location function args source result sourceNext nextFunction nextArgs target ⟨run, noType⟩
      ⟨related, loc, argsRel, states⟩
    subst location
    exact evaluate_simulation.2 function nextFunction args nextArgs source target result sourceNext
      run noType related argsRel states

end Flapjack.Compiler.Backend.ClosNumber
