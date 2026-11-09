module

public import Flapjack.Compiler.Backend.ClosLetop.Proofs.EvaluateBasic
public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Primitive
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClockShift

@[expose] public section

/-! Ordinary-operation case of closure let-operation correctness. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Ordinary operations simulate after related argument evaluation. This
Flapjack helper isolates the non-install, non-forcing dispatcher branch of
the HOL operation case. -/
theorem evaluate_ordinary_op {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List Value) (source : State C F)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate args env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel args code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.op trace op args] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel [.op trace op args] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.op trace op (compileList args)] := by
    simpa [CodeRel, compileList, compileSing] using code
  rw [codeEq, evaluate_ordinaryOp_eq trace op _ _ _ notInstall notForce]
  rw [evaluate_ordinaryOp_eq trace op _ _ _ notInstall notForce] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    obtain ⟨targetArgsResult, targetMiddle, targetArgsRun, argsRel, middleRel⟩ :=
      argsIH argsResult middle (compileList args) nextEnv target
        ⟨argsRun, envRel, states, rfl⟩
    rw [argsRun] at run
    rw [targetArgsRun]
    cases argsResult with
    | err error =>
      cases run
      cases targetArgsResult with
      | val values => cases error <;> simp [ResultRel] at argsRel
      | err targetError => exact ⟨.err targetError, targetMiddle, rfl, argsRel, middleRel⟩
    | val values =>
      cases targetArgsResult with
      | err error => cases error <;> simp [ResultRel] at argsRel
      | val targetValues =>
        have step := PrimitivePort.doAppLemma middle targetMiddle values.reverse targetValues.reverse op
          ⟨middleRel, List.rel_reverse argsRel⟩
        cases appRun : doApp op values.reverse middle with
        | err error =>
          simp only [appRun] at step run
          cases run
          obtain ⟨targetError, targetApp, errors⟩ := step
          refine ⟨.err targetError, targetMiddle, ?_, ?_, middleRel⟩
          · simp [targetApp]
          · cases error <;> cases targetError <;>
              simp_all [ResultRel, Flapjack.SemanticPrimitivesProps.excRel]
        | val pair =>
          rcases pair with ⟨value, last⟩
          simp only [appRun] at step run
          cases run
          obtain ⟨targetValue, targetLast, valuesRel, lastRel, targetApp⟩ := step
          exact ⟨.val [targetValue], targetLast, by simp [targetApp], .cons valuesRel .nil, lastRel⟩

end Flapjack.Compiler.Backend.ClosLetop
