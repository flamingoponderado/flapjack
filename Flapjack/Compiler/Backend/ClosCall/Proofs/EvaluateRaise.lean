module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateTick
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section

/-! Exception-raising evaluation for direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- Matching raises simulate when their bodies simulate. -/
theorem exprSimFuel_raise {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (sourceBody targetBody : ClosLang.Exp)
    (bodyIH : ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody) :
    ExprSimFuel (C := C) (F := F) fuel g allowed (.raise trace sourceBody) (.raise trace targetBody) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs states
  have bodyEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)] := by
    apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
    have h := (envRelFuel_iff fuel g allowed target.code sourceEnv targetEnv 0
      [(0, .raise trace targetBody)]).mp envs
    simpa [envRel, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] using h
  cases bodyRun : evaluate [sourceBody] sourceEnv source with
  | mk bodyResult bodyFinal =>
    have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      have : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, bodyRun] using congrArg Prod.fst run.symm
      exact notType this
    obtain ⟨targetResult, targetFinal, targetRun, results, finalStates, codeGrowth⟩ :=
      bodyIH sourceEnv targetEnv source target bodyResult bodyFinal bodyRun bodyNotType bodyEnv states
    cases bodyResult with
    | err error =>
      cases targetResult with
      | val values => simp [resultRel] at results
      | err targetError =>
        have sourceEq : sourceResult = .err error ∧ sourceFinal = bodyFinal := by
          simpa [evaluate, bodyRun] using run.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨.err targetError, targetFinal, ?_, results, finalStates, codeGrowth⟩
        simp [evaluate, targetRun]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value sourceBody sourceEnv source bodyFinal values bodyRun
      cases targetResult with
      | err error => simp [resultRel] at results
      | val targetValues =>
        obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetBody targetEnv target targetFinal targetValues targetRun
        have sourceEq : sourceResult = .err (.raise value) ∧ sourceFinal = bodyFinal := by
          simpa [evaluate, bodyRun] using run.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        have valuesRel : ValueRelFuel fuel g allowed targetFinal.code value targetValue := by
          simpa [resultRel] using results
        refine ⟨.err (.raise targetValue), targetFinal, ?_, ?_, finalStates, codeGrowth⟩
        · simp [evaluate, targetRun]
        · exact valuesRel

end Flapjack.Compiler.Backend.ClosCall
