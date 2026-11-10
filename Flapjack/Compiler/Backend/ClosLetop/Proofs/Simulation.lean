module

public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Apply
public import Flapjack.Compiler.Backend.ClosLetop.Proofs.EvaluateLetrec
public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Production

@[expose] public section

/-! Mutual evaluator simulation for closure let-operation cleanup. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open Flapjack.Compiler.Backend.ClosSem AppPort OpPort
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Mutual simulation factored through fixed-state predicates for the
well-founded induction. This Lean-side theorem has no standalone HOL declaration. -/
theorem evaluate_simulation {C F : Type} :
    (∀ expressions env (source : State C F), EvalAt expressions env source) ∧
      (∀ location function args (source : State C F), AppAt location function args source) := by
  have all : ∀ clock : Nat,
      (∀ (source : State C F), source.clock = clock → ∀ location function args, AppAt location function args source) ∧
      (∀ weight expressions env (source : State C F),
        source.clock = clock → expsWeight expressions = weight → EvalAt expressions env source) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ (source : State C F), source.clock = clock →
          ∀ location function args, AppAt location function args source := by
        intro source clockEq location function args
        cases args with
        | nil =>
          intro result next targetFunction targetArgs target premises
          exact evaluate_let_op_app_nil location function targetFunction source result next targetArgs target premises
        | cons arg rest =>
          apply evaluate_let_op_app_cons location function arg rest source
          · intro body env remaining closureRun enough
            have positive : 0 < (arg :: rest).length - remaining.length :=
              Nat.sub_pos_of_lt (destClosure_full_remaining_lt _ _ _ _ _ _ _ closureRun)
            have smaller : (decClock ((arg :: rest).length - remaining.length) source).clock < clock := by
              simp only [decClock, clockEq, List.length_cons] at positive enough ⊢
              omega
            exact (clockIH _ smaller).2 (expsWeight [body]) [body] env _ rfl rfl
          · intro body env remaining value middle closureRun enough bodyRun
            have positive : 0 < (arg :: rest).length - remaining.length :=
              Nat.sub_pos_of_lt (destClosure_full_remaining_lt _ _ _ _ _ _ _ closureRun)
            have bound := evaluate_clock_le [body] env (decClock ((arg :: rest).length - remaining.length) source)
            have smaller : middle.clock < clock := by
              rw [bodyRun] at bound
              have before : middle.clock ≤ (decClock ((arg :: rest).length - remaining.length) source).clock := by
                exact bound
              simp only [decClock, clockEq, List.length_cons] at before positive enough
              omega
            exact (clockIH _ smaller).1 middle rfl location value remaining
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ expressions env (state : State C F),
              state.clock ≤ clock → expsWeight expressions < weight → EvalAt expressions env state := by
            intro expressions env state clockLe weightLt
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions env state rfl rfl
            · exact weightIH (expsWeight expressions) weightLt expressions env state clockEq rfl
          intro expressions env source clockEq measure
          cases expressions with
          | nil =>
            intro result next code nextEnv target premises
            exact evaluate_let_op_nil env nextEnv source result next code target premises
          | cons first rest =>
            cases rest with
            | cons second tail =>
              intro result next code nextEnv target premises
              apply evaluate_let_op_cons first second tail env source ?_ ?_ result next code nextEnv target premises
              · apply exprIH [first] env source (by omega)
                simp only [expsWeight] at measure ⊢; omega
              · intro values middle firstRun
                apply exprIH (second :: tail) env middle
                · have bound := evaluate_clock_le [first] env source
                  simpa [firstRun, clockEq] using bound
                · simp only [expsWeight] at measure ⊢; omega
            | nil =>
              cases first with
              | var trace index =>
                intro result next code nextEnv target premises
                exact evaluate_let_op_var trace index env nextEnv source result next code target premises
              | fn name location selected arity body =>
                intro result next code nextEnv target premises
                exact evaluate_let_op_fn name location selected arity body env nextEnv source result next code target premises
              | raise trace body =>
                intro result next code nextEnv target premises
                apply evaluate_let_op_raise trace body env source ?_ result next code nextEnv target premises
                apply exprIH [body] env source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | tick trace body =>
                intro result next code nextEnv target premises
                apply evaluate_let_op_tick trace body env source ?_ result next code nextEnv target premises
                intro nonzero
                apply exprIH [body] env (decClock 1 source) (by simp [decClock]; omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | call trace ticks location args =>
                intro result next code nextEnv target premises
                apply evaluate_let_op_call trace ticks location args env source ?_ result next code nextEnv target premises
                apply exprIH args env source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | «let» trace bindings body =>
                intro result next code nextEnv target premises
                apply evaluate_let_op_let trace bindings body env source ?_ ?_ result next nextEnv target code premises
                · intro ihResult ihNext ihEnv ihTarget ihCode ihPremises
                  apply exprIH bindings env source (by omega) ?_ ihResult ihNext ihCode ihEnv ihTarget ihPremises
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro values middle bindingsRun ihResult ihNext ihEnv ihTarget ihCode ihPremises
                  apply exprIH [body] (values ++ env) middle ?_ ?_ ihResult ihNext ihCode ihEnv ihTarget ihPremises
                  · have bound := evaluate_clock_le bindings env source
                    simpa [bindingsRun, clockEq] using bound
                  · simp only [expsWeight, expWeight] at measure ⊢; omega
              | letrec names location selected functions body =>
                intro result next code nextEnv target premises
                apply evaluate_let_op_letrec names location selected functions body env source ?_
                  result next code nextEnv target premises
                intro buildRc envdelta ed arity builder delta capture
                apply exprIH [body] (ed ++ env) source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | handle trace body handler =>
                intro result next code nextEnv target premises
                apply evaluate_let_op_handle trace body handler env source ?_ ?_ result next code nextEnv target premises
                · apply exprIH [body] env source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro value middle bodyRun
                  apply exprIH [handler] (value :: env) middle
                  · have bound := evaluate_clock_le [body] env source
                    simpa [bodyRun, clockEq] using bound
                  · simp only [expsWeight, expWeight] at measure ⊢; omega
              | ifThenElse trace condition yes no =>
                intro result next code nextEnv target premises
                apply evaluate_let_op_if trace condition yes no env source ?_ ?_ ?_ result next code nextEnv target premises
                · apply exprIH [condition] env source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro values middle conditionRun decision
                  apply exprIH [yes] env middle
                  · have bound := evaluate_clock_le [condition] env source
                    simpa [conditionRun, clockEq] using bound
                  · simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro values middle conditionRun notTrue decision
                  apply exprIH [no] env middle
                  · have bound := evaluate_clock_le [condition] env source
                    simpa [conditionRun, clockEq] using bound
                  · simp only [expsWeight, expWeight] at measure ⊢; omega
              | app trace location function args =>
                intro result next code nextEnv target premises
                apply evaluate_let_op_app trace location function args env source ?_ ?_ ?_
                  result next code nextEnv target premises
                · intro nonempty
                  apply exprIH args env source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro values middle nonempty argsRun
                  apply exprIH [function] env middle
                  · have bound := evaluate_clock_le args env source
                    simpa [argsRun, clockEq] using bound
                  · simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro values middle functions last nonempty argsRun functionRun
                  have firstBound := evaluate_clock_le args env source
                  have secondBound := evaluate_clock_le [function] env middle
                  have bound : last.clock ≤ clock := by
                    have one : middle.clock ≤ source.clock := by simpa [argsRun] using firstBound
                    have two : last.clock ≤ middle.clock := by simpa [functionRun] using secondBound
                    omega
                  rcases Nat.lt_or_eq_of_le bound with smaller | equal
                  · exact (clockIH last.clock smaller).1 last rfl location _ values
                  · exact appAll last equal location _ values
              | op trace op args =>
                apply evaluate_let_op_op trace op args env source
                · apply exprIH args env source (by omega)
                  have smaller := opWeight_gt trace op args
                  simp only [expsWeight] at measure
                  omega
                · intro values middle program installed argsRun opEq installRun
                  have argsClock := evaluate_clock_le args env source
                  have installClock := doInstall_success_clock values.reverse middle installed program installRun
                  have smaller : installed.clock < clock := by
                    have middleLe : middle.clock ≤ source.clock := by simpa [argsRun] using argsClock
                    omega
                  exact (clockIH installed.clock smaller).2 (expsWeight program) program [] installed rfl rfl
                · intro values middle value argsRun notInstall opEq thunkRun
                  subst op
                  apply exprIH [appUnit (.var .none 0)] [value] middle
                  · have bound := evaluate_clock_le args env source
                    simpa [argsRun, clockEq] using bound
                  · have h := appUnit_var_weight
                    simp only [expsWeight, expWeight] at measure
                    simp only [appUnit, expsWeight, expWeight] at h ⊢
                    omega
  constructor
  · intro expressions env source
    exact (all source.clock).2 (expsWeight expressions) expressions env source rfl rfl
  · intro location function args source
    exact (all source.clock).1 source rfl location function args

namespace SimulationPort
/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Let-operation cleanup simulates both expression evaluation and closure
application, including errors and final state relations. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op {C F : Type} :
    (∀ (xs : List ClosLang.Exp) (env : List Value) (source : State C F)
      (result : Result (List Value) Value) (next : State C F) (code : List ClosLang.Exp)
      (nextEnv : List Value) (target : State C F),
      evaluate xs env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel xs code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext) ∧
    (∀ (location : Option Nat) (function : Value) (args : List Value) (source : State C F)
      (result : Result (List Value) Value) (next : State C F) (targetFunction : Value)
      (targetArgs : List Value) (target : State C F),
      evaluateApp location function args source = (result, next) ∧ ValueRel function targetFunction ∧
        List.Forall₂ ValueRel args targetArgs ∧ StateRel source target →
      ∃ targetResult targetNext, evaluateApp location targetFunction targetArgs target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext) := by
  constructor
  · intro xs env source result next code nextEnv target premises
    exact evaluate_simulation.1 xs env source result next code nextEnv target premises
  · intro location function args source result next targetFunction targetArgs target premises
    exact evaluate_simulation.2 location function args source result next targetFunction targetArgs target premises

/-- The evaluator simulation specialized to the executable source traversal. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "let_op_correct"
  (fmap_as_finite_support := [refs, code])]
theorem let_op_correct {C F : Type} (xs : List ClosLang.Exp) (env : List Value)
    (source : State C F) (result : Result (List Value) Value) (next : State C F)
    (nextEnv : List Value) (target : State C F)
    (premises : evaluate xs env source = (result, next) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target) :
    ∃ targetResult targetNext,
      evaluate (compileSource xs) nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel next targetNext := by
  exact evaluate_let_op.1 xs env source result next (compileSource xs) nextEnv target
    ⟨premises.1, premises.2.1, premises.2.2, rfl⟩
end SimulationPort

end Flapjack.Compiler.Backend.ClosLetop
