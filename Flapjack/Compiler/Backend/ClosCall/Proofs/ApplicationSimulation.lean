import Flapjack.Compiler.Backend.ClosCall.Proofs.DirectCallImpureSimulation
import Flapjack.Compiler.Backend.ClosCall.Proofs.DirectCallPureSimulation

/-! Application traversal simulation for all direct-call rewrite choices. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- The actual application traversal simulates source evaluation for every
location and purity branch, given recursive simulations and a well-formed
source environment. The fixed compiler-state relation, the environment
invariant, and the body induction hypothesis remain assumptions; this is not
the complete HOL growing-state or oracle simulation. -/
theorem callsFuel_app_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (location : Option Nat) (sourceFn : ClosLang.Exp)
    (sourceArgs : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace location sourceFn sourceArgs) initial = some (out, final))
    (notAllowed : ∀ address, location = some address →
      (sptLookup address final.1).isSome = true → address ∉ allowed)
    (distinct : (g.2.map Prod.fst).Nodup)
    (argsIH : ∀ targetArgs middle, callsListFuel fuel sourceArgs initial = some (targetArgs, middle) →
      ExprsSimFuel (C := C) (F := F) fuel g allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel fuel sourceFn middle = some (targetFn, final) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceFn targetFn)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (sourceBody targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody)
    (sourceEnv targetEnv : List ClosSem.Value) (source : ClosSem.State (NumSet × C) F)
    (target : ClosSem.State C F) (sourceResult : Result (List ClosSem.Value) ClosSem.Value)
    (sourceFinal : ClosSem.State (NumSet × C) F)
    (sourceRun : evaluate [.app trace location sourceFn sourceArgs] sourceEnv source = (sourceResult, sourceFinal))
    (notType : sourceResult ≠ .err (.abort .typeError))
    (envs : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (wf : ValuesWellFormedFuel fuel g allowed target.code sourceEnv)
    (states : StateRelFuel fuel g allowed source target) :
    ∃ targetResult targetFinal,
      evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, target.code.lookup key = some value → targetFinal.code.lookup key = some value) := by
  cases location with
  | none =>
    obtain ⟨targetFn, targetArgs, rfl, sim⟩ :=
      callsFuel_app_none_sim fuel g allowed trace sourceFn sourceArgs initial final out run distinct argsIH fnIH bodyIH
    exact sim sourceEnv targetEnv source target sourceResult sourceFinal sourceRun notType envs states
  | some address =>
    cases found : sptLookup address final.1 with
    | none =>
      obtain ⟨targetFn, targetArgs, rfl, sim⟩ :=
        callsFuel_app_unknown_sim fuel g allowed trace address sourceFn sourceArgs initial final out run found distinct argsIH fnIH bodyIH
      exact sim sourceEnv targetEnv source target sourceResult sourceFinal sourceRun notType envs states
    | some value =>
      have known : (sptLookup address final.1).isSome = true := by simp [found]
      cases purity : ClosLang.pure sourceFn with
      | false =>
        have sim := callsFuel_app_impure_sim fuel g allowed trace address sourceFn sourceArgs initial final out
          run known purity (notAllowed address rfl known) distinct argsIH fnIH bodyIH
        exact sim sourceEnv targetEnv source target sourceResult sourceFinal sourceRun notType envs states
      | true =>
        exact callsFuel_app_pure_sim fuel g allowed trace address sourceFn sourceArgs initial final out
          run known purity (notAllowed address rfl known) distinct argsIH fnIH bodyIH
          sourceEnv targetEnv source target sourceResult sourceFinal sourceRun notType envs wf states

end Flapjack.Compiler.Backend.ClosCall
