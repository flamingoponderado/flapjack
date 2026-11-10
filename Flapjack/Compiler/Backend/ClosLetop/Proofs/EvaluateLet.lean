module

public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Relations
public import Flapjack.Compiler.Backend.ClosLetop.Proofs.VarListEvaluate

@[expose] public section

/-! Let case of closure let-operation correctness. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- The result relation instantiated to related closure values. This
specialization is Lean-side infrastructure, not a standalone HOL declaration. -/
def ResultRel : Result (List Value) Value → Result (List Value) Value → Prop
  | .val left, .val right => List.Forall₂ ValueRel left right
  | .err (.raise left), .err (.raise right) => ValueRel left right
  | .err (.abort left), .err (.abort right) => left = right
  | _, _ => False

namespace LetPort
/-- The closure state's canonical finite-map representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end LetPort

/-- The let case of the original forward simulation. The two induction
hypotheses follow the source evaluator's bindings and successful body cases. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op_let {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (envSource : List Value) (source : State C F)
    (bindingsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (envTarget : List Value) (target : State C F) (code : List ClosLang.Exp),
      evaluate bindings envSource source = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
        StateRel source target ∧ CodeRel bindings code →
      ∃ targetResult targetNext,
        evaluate code envTarget target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (bodyIH : ∀ (values : List Value) (middle : State C F),
      evaluate bindings envSource source = (.val values, middle) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (envTarget : List Value) (target : State C F) (code : List ClosLang.Exp),
        evaluate [body] (values ++ envSource) middle = (result, next) ∧
          List.Forall₂ ValueRel (values ++ envSource) envTarget ∧ StateRel middle target ∧
          CodeRel [body] code →
        ∃ targetResult targetNext,
          evaluate code envTarget target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (envTarget : List Value) (target : State C F) (targetCode : List ClosLang.Exp)
    (premises : evaluate [.let trace bindings body] envSource source = (result, sourceNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel [.let trace bindings body] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode envTarget target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [compileSing (.let trace bindings body)] := by
    simpa [CodeRel, compileList] using code
  clear code
  subst targetCode
  cases bindingsRun : evaluate bindings envSource source with
  | mk bindingsResult sourceMiddle =>
    obtain ⟨targetResult, targetMiddle, targetRun, related, middleRel⟩ :=
      bindingsIH bindingsResult sourceMiddle envTarget target (compileList bindings)
        ⟨bindingsRun, envRel, states, by simp [CodeRel]⟩
    cases bindingsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, bindingsRun] at run
      cases run
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at related
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, related, middleRel⟩
        change evaluate [match destOp (compileSing body) (compileList bindings) with
          | some op => .op trace op (compileList bindings)
          | none => .let trace (compileList bindings) (compileSing body)] envTarget target = _
        cases transformed : compileSing body <;> simp only [destOp] <;>
          (try split) <;> rw [evaluate, fixClock_evaluate, targetRun]
    | val values =>
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at related
      | val targetValues =>
        have bodyRun : evaluate [body] (values ++ envSource) sourceMiddle = (result, sourceNext) := by
          rw [evaluate, fixClock_evaluate, bindingsRun] at run
          exact run
        obtain ⟨bodyResult, bodyNext, targetBodyRun, resultRel, finalRel⟩ :=
          bodyIH values sourceMiddle bindingsRun result sourceNext (targetValues ++ envTarget) targetMiddle
            [compileSing body] ⟨bodyRun, List.rel_append related envRel, middleRel, by simp [CodeRel, compileList]⟩
        refine ⟨bodyResult, bodyNext, ?_, resultRel, finalRel⟩
        change evaluate [match destOp (compileSing body) (compileList bindings) with
          | some op => .op trace op (compileList bindings)
          | none => .let trace (compileList bindings) (compileSing body)] envTarget target = _
        cases transformed : compileSing body with
        | op opTrace op args =>
          by_cases valid : varList 0 args (compileList bindings) = true
          · simp only [destOp, valid, if_true]
            have reduction := Proofs.evaluateLetOpReduction (compileList bindings) args trace opTrace op
              envTarget target valid
            rw [← reduction, evaluate, fixClock_evaluate, targetRun]
            simpa [transformed] using targetBodyRun
          · have bad : varList 0 args (compileList bindings) = false := by
              cases h : varList 0 args (compileList bindings) <;> simp_all
            simp only [destOp, bad, Bool.false_eq_true, if_false]
            rw [evaluate, fixClock_evaluate, targetRun]
            simpa [transformed] using targetBodyRun
        | _ =>
          simp only [destOp]
          rw [evaluate, fixClock_evaluate, targetRun]
          simpa [transformed] using targetBodyRun

end Flapjack.Compiler.Backend.ClosLetop
