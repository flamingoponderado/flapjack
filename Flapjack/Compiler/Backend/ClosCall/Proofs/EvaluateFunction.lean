import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateLet

/-! Function-creation evaluation for direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- The free variables needed by a function are precisely those needed by its
body after the argument slots. -/
theorem envRelFuel_fn_body {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    (name : Basis.Pure.MlString.MlString) (loc : Option Nat) (arity : Nat) (body : ClosLang.Exp)
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 [(0, .fn name loc none arity body)]) :
    EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 [(arity, body)] := by
  apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
  have h := (envRelFuel_iff _ _ _ _ _ _ _ _).mp related
  unfold envRel at h ⊢
  by_cases same : sourceEnv.length = targetEnv.length
  · simpa [same] using h
  simp only [same, ↓reduceIte] at h ⊢
  intro x used
  apply h x
  simp only [List.mem_singleton, exists_eq_left, Nat.zero_add] at used ⊢
  simp only [ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp, or_false] at used ⊢
  simpa [Nat.add_comm] using used

/-- A function-creation evaluation is simulated once the pass invariant has
established the recursive-closure relation for its original and transformed
bodies. The relation premise is a remaining compiler-invariant obligation;
this helper is not the full HOL function case. -/
theorem evaluate_fn_fuel {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (name : Basis.Pure.MlString.MlString) (loc arity : Nat) (sourceBody targetBody : ClosLang.Exp)
    (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value) (sourceFinal : ClosSem.State (NumSet × C) F)
    (sourceRun : evaluate [.fn name (some loc) none arity sourceBody] sourceEnv source = (sourceResult, sourceFinal))
    (notType : sourceResult ≠ .err (.abort .typeError))
    (envs : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0
      [(0, .fn name (some loc) none arity targetBody)])
    (states : StateRelFuel fuel g allowed source target)
    (closure : recClosureRelFuel fuel g allowed target.code loc [(arity, sourceBody)] [(arity, targetBody)]) :
    ∃ targetResult targetFinal,
      evaluate [.fn name (some loc) none arity targetBody] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, target.code.lookup key = some value → targetFinal.code.lookup key = some value) := by
  have valid : arity ≤ source.maxApp ∧ arity ≠ 0 := by
    by_contra invalid
    have bad : sourceResult = .err (.abort .typeError) := by
      simpa [evaluate, invalid] using congrArg Prod.fst sourceRun.symm
    exact notType bad
  have targetValid : arity ≤ target.maxApp ∧ arity ≠ 0 := by
    simpa [← states.2.2.1] using valid
  have sourceEq : sourceResult = .val [.closure (some loc) [] sourceEnv arity sourceBody] ∧
      sourceFinal = source := by
    simpa [evaluate, valid] using sourceRun.symm
  obtain ⟨rfl, rfl⟩ := sourceEq
  have captured := envRelFuel_fn_body name (some loc) arity targetBody envs
  have values : ValueRelFuel fuel g allowed target.code
      (.closure (some loc) [] sourceEnv arity sourceBody)
      (.closure (some loc) [] targetEnv arity targetBody) := .closure closure .nil captured
  refine ⟨.val [.closure (some loc) [] targetEnv arity targetBody], target, ?_, ?_, states, fun _ _ h => h⟩
  · simp [evaluate, targetValid]
  · exact .cons values .nil

end Flapjack.Compiler.Backend.ClosCall
