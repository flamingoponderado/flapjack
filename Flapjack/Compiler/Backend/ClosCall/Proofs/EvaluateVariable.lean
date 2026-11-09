import Flapjack.Compiler.Backend.ClosCall.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import Flapjack.SemanticPrimitivesProps.ResultRelation

/-! Variable evaluation for the fuel-aware direct-call simulation. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- Empty expression lists evaluate to related empty results and preserve
the related states. -/
theorem evaluate_nil_fuel {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (states : StateRelFuel fuel g allowed source target) :
    evaluate [] sourceEnv source = (.val [], source) ∧
      evaluate [] targetEnv target = (.val [], target) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed target.code))
        (ValueRelFuel fuel g allowed target.code) (.val []) (.val []) ∧
      StateRelFuel fuel g allowed source target := by
  exact ⟨by simp [evaluate], by simp [evaluate], .nil, states⟩

/-- A used source variable that evaluates without a type error is matched by
the same variable in the target environment. Both evaluations preserve their
states. This is fuel-aware infrastructure for the direct-call simulation;
the evaluator and bounded pass correspondence are not claimed as HOL ports. -/
theorem evaluate_var_fuel {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (index : Nat) (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value) (sourceFinal : ClosSem.State (NumSet × C) F)
    (sourceRun : evaluate [.var trace index] sourceEnv source = (sourceResult, sourceFinal))
    (notTypeError : sourceResult ≠ .err (.abort .typeError))
    (envs : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, .var trace index)])
    (states : StateRelFuel fuel g allowed source target) :
    ∃ targetResult targetFinal,
      evaluate [.var trace index] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed target.code))
        (ValueRelFuel fuel g allowed target.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal := by
  cases lookup : sourceEnv[index]? with
  | none =>
    have failed : sourceResult = .err (.abort .typeError) := by
      simpa [evaluate, lookup] using congrArg Prod.fst sourceRun.symm
    exact False.elim (notTypeError failed)
  | some value =>
    have sourceEq : sourceResult = .val [value] ∧ sourceFinal = source := by
      simpa [evaluate, lookup] using sourceRun.symm
    obtain ⟨rfl, rfl⟩ := sourceEq
    have related := (envRelFuel_iff fuel g allowed target.code sourceEnv targetEnv 0
      [(0, .var trace index)]).mp envs
    have used : ∃ fn ∈ [(0, .var trace index)],
        ClosProps.freeVar (fn.1 + 0 + index) fn.2 := by
      refine ⟨(0, .var trace index), by simp, ?_⟩
      simp [ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp]
    obtain ⟨next, nextLookup, values⟩ := envRel_lookup related used lookup
    refine ⟨.val [next], target, ?_, ?_, states⟩
    · simp [evaluate, nextLookup]
    · exact List.Forall₂.cons values .nil

end Flapjack.Compiler.Backend.ClosCall
