module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Operation
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateRaise
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateHandle
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateLet
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateIf
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateLetrec
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateApp
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateCall
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateTick

@[expose] public section

/-! Mutual evaluator simulation for closure tick removal. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem OpPort
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Mutual simulation factored through fixed-state predicates for the
well-founded induction. -/
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
          exact evaluate_remove_ticks_app_nil location function source result next targetFunction targetArgs target premises
        | cons arg rest =>
          apply evaluate_remove_ticks_app_cons location function arg rest source
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
            intro result next nextEnv target code premises
            exact evaluate_remove_ticks_nil env source result next nextEnv target code premises
          | cons first rest =>
            cases rest with
            | cons second tail =>
              intro result next nextEnv target code premises
              apply evaluate_remove_ticks_cons first second tail env source ?_ ?_ result next nextEnv target code premises
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
                intro result next nextEnv target code premises
                exact evaluate_remove_ticks_var trace index env source result next nextEnv target code premises
              | fn name location selected arity body =>
                intro result next nextEnv target code premises
                exact evaluate_remove_ticks_fn name location selected arity body env source result next nextEnv target code premises
              | raise trace body =>
                intro result next nextEnv target code premises
                apply evaluate_remove_ticks_raise trace body env source ?_ result next nextEnv target code premises
                apply exprIH [body] env source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | tick trace body =>
                intro result next nextEnv target code premises
                exact evaluate_remove_ticks_tick trace body env source result next nextEnv target code premises
              | call trace ticks location args =>
                intro result next nextEnv target code premises
                apply evaluate_remove_ticks_call trace ticks location args env source ?_ result next nextEnv target code premises
                apply exprIH args env source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | «let» trace bindings body =>
                intro result next nextEnv target code premises
                apply evaluate_remove_ticks_let trace bindings body env source ?_ ?_ result next nextEnv target code premises
                · apply exprIH bindings env source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro values middle bindingsRun
                  apply exprIH [body] (values ++ env) middle
                  · have bound := evaluate_clock_le bindings env source
                    simpa [bindingsRun, clockEq] using bound
                  · simp only [expsWeight, expWeight] at measure ⊢; omega
              | letrec names location selected functions body =>
                intro result next nextEnv target code premises
                apply evaluate_remove_ticks_letrec names location selected functions body env source ?_
                  result next nextEnv target code premises
                intro buildRc envdelta ed arity builder delta capture
                apply exprIH [body] (ed ++ env) source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | handle trace body handler =>
                intro result next nextEnv target code premises
                apply evaluate_remove_ticks_handle trace body handler env source ?_ ?_ result next nextEnv target code premises
                · apply exprIH [body] env source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro value middle bodyRun
                  apply exprIH [handler] (value :: env) middle
                  · have bound := evaluate_clock_le [body] env source
                    simpa [bodyRun, clockEq] using bound
                  · simp only [expsWeight, expWeight] at measure ⊢; omega
              | ifThenElse trace condition yes no =>
                intro result next nextEnv target code premises
                apply evaluate_remove_ticks_if trace condition yes no env source ?_ ?_ ?_ result next nextEnv target code premises
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
                intro result next nextEnv target code premises
                apply evaluate_remove_ticks_app trace location function args env source ?_ ?_ ?_
                  result next nextEnv target code premises
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
                apply evaluate_remove_ticks_op trace op args env source
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
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Tick removal simulates both expression evaluation and closure
application in the original reverse direction. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks {C F : Type} :
    (∀ (ys : List ClosLang.Exp) (envTarget : List Value) (target : State C F)
      (result : Result (List Value) Value) (next : State C F) (envSource : List Value)
      (source : State C F) (xs : List ClosLang.Exp),
      evaluate ys envTarget target = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
        StateRel source target ∧ CodeRel xs ys →
      ∃ extra sourceResult sourceNext,
        evaluate xs envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
        ResultRel sourceResult result ∧ StateRel sourceNext next) ∧
    (∀ (location : Option Nat) (function : Value) (args : List Value) (target : State C F)
      (result : Result (List Value) Value) (next : State C F) (sourceFunction : Value)
      (sourceArgs : List Value) (source : State C F),
      evaluateApp location function args target = (result, next) ∧ ValueRel sourceFunction function ∧
        List.Forall₂ ValueRel sourceArgs args ∧ StateRel source target →
      ∃ extra sourceResult sourceNext,
        evaluateApp location sourceFunction sourceArgs { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
        ResultRel sourceResult result ∧ StateRel sourceNext next) := by
  exact evaluate_simulation

/-- Tick removal simulates the evaluator for a source program. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_correct"
  (fmap_as_finite_support := [refs, code])]
theorem remove_ticks_correct {C F : Type} (xs : List ClosLang.Exp) (envTarget : List Value)
    (target : State C F) (result : Result (List Value) Value) (next : State C F)
    (envSource : List Value) (source : State C F)
    (premises : evaluate (removeList xs) envTarget target = (result, next) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target) :
    ∃ extra sourceResult sourceNext,
      evaluate xs envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext next := by
  exact evaluate_remove_ticks.1 (removeList xs) envTarget target result next envSource source xs
    ⟨premises.1, premises.2.1, premises.2.2, rfl⟩
end SimulationPort

/-- The executed bounded-retry traversal is the code covered by the evaluator
simulation. This is Flapjack infrastructure connecting the production path. -/
theorem removeBounded_correct {C F : Type} (fuel : Nat) (xs : List ClosLang.Exp) (envTarget : List Value)
    (target : State C F) (result : Result (List Value) Value) (next : State C F)
    (envSource : List Value) (source : State C F)
    (premises : evaluate (removeList xs) envTarget target = (result, next) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target) :
    ∃ code extra sourceResult sourceNext,
      xs.mapM (removeBounded fuel) = some code ∧ evaluate code envTarget target = (result, next) ∧
      evaluate xs envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext next := by
  obtain ⟨extra, sourceResult, sourceNext, run, results, states⟩ :=
    SimulationPort.remove_ticks_correct xs envTarget target result next envSource source premises
  exact ⟨removeList xs, extra, sourceResult, sourceNext,
    removeBounded_list_eq_source fuel xs, premises.1, run, results, states⟩

end Flapjack.Compiler.Backend.ClosTicks

