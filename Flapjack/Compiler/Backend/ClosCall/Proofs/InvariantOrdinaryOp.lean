import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantControlSimulation
import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveTotal

/-! Direct-call simulation of ordinary primitive operations. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem ClosProps SemanticPrimitivesHOL SemanticPrimitivesProps

/-- The environment relation for a primitive expression covers its arguments. -/
theorem envRelFuel_op_args {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    (trace : BackendCommon.Tra) (op : ClosLang.Op) (args : List ClosLang.Exp)
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 [(0, .op trace op args)]) :
    EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 (args.map (0, ·)) := by
  apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
  have h := (envRelFuel_iff _ _ _ _ _ _ _ _).mp related
  unfold envRel at h ⊢
  by_cases same : sourceEnv.length = targetEnv.length
  · simpa [same] using h
  simp only [same, ↓reduceIte] at h ⊢
  intro x ⟨item, member, free⟩
  obtain ⟨expr, exprMember, rfl⟩ := List.mem_map.mp member
  apply h x
  refine ⟨(0, .op trace op args), by simp, ?_⟩
  simp only [Nat.zero_add, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp, or_false] at free ⊢
  exact freeVars_of_mem x expr args exprMember free

/-- Ordinary primitive expressions simulate under the source invariant when
their argument lists simulate. Install and force-thunk need their separate
evaluator cases. This is Lean-side infrastructure, not the full HOL result. -/
theorem exprSimFuelInvariant_ordinaryOp {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (op : ClosLang.Op) (sourceArgs targetArgs : List ClosLang.Exp)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed sourceArgs targetArgs) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed
      (.op trace op sourceArgs) (.op trace op targetArgs) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf sourceWf states
  have argsEnv := envRelFuel_op_args trace op targetArgs envs
  rw [evaluate_ordinaryOp_eq trace op sourceArgs sourceEnv source notInstall notForce] at run
  cases argsRun : evaluate sourceArgs sourceEnv source with
  | mk argsResult argsFinal =>
    have argsNotType : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have : sourceResult = .err (.abort .typeError) := by
        simpa [argsRun] using congrArg Prod.fst run.symm
      exact notType this
    obtain ⟨targetArgsResult, targetArgsFinal, targetArgsRun, argsRel, argsStates, argsGrowth⟩ :=
      argsIH sourceEnv targetEnv source target argsResult argsFinal argsRun argsNotType argsEnv envWf sourceWf states
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val values => simp [resultRel] at argsRel
      | err targetError =>
        have sourceEq : sourceResult = .err error ∧ sourceFinal = argsFinal := by simpa [argsRun] using run.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨.err targetError, targetArgsFinal, ?_, argsRel, argsStates, argsGrowth⟩
        simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce, targetArgsRun]
    | val sourceValues =>
      cases targetArgsResult with
      | err error => simp [resultRel] at argsRel
      | val targetValues =>
        have values : List.Forall₂ (ValueRelFuel fuel g allowed targetArgsFinal.code)
            sourceValues.reverse targetValues.reverse := List.rel_reverse argsRel
        have sim := ClosProps.PrimitiveTotal.simpleValRelDoApp
          (ValueRelFuel fuel g allowed targetArgsFinal.code)
          (fun (s : ClosSem.State (NumSet × C) F) (t : ClosSem.State C F) =>
            t.code = targetArgsFinal.code ∧ StateRelFuel fuel g allowed s t)
          argsFinal targetArgsFinal sourceValues.reverse targetValues.reverse op
          ⟨valueRelFuel_simple fuel g allowed targetArgsFinal.code,
            stateRelFuel_simple fuel g allowed targetArgsFinal.code⟩ ⟨⟨rfl, argsStates⟩, values⟩
        cases primRun : doApp op sourceValues.reverse argsFinal with
        | err error =>
          simp only [primRun] at sim
          obtain ⟨targetError, targetPrim, errors⟩ := sim
          have sourceEq : sourceResult = .err error ∧ sourceFinal = argsFinal := by
            simpa [argsRun, primRun] using run.symm
          obtain ⟨rfl, rfl⟩ := sourceEq
          refine ⟨.err targetError, targetArgsFinal, ?_, errors, argsStates, argsGrowth⟩
          simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce, targetArgsRun, targetPrim]
        | val pair =>
          obtain ⟨value, final⟩ := pair
          simp only [primRun] at sim
          obtain ⟨targetValue, targetFinal, valueRel, ⟨codeEq, finalStates⟩, targetPrim⟩ := sim
          have sourceEq : sourceResult = .val [value] ∧ sourceFinal = final := by
            simpa [argsRun, primRun] using run.symm
          obtain ⟨rfl, rfl⟩ := sourceEq
          refine ⟨.val [targetValue], targetFinal, ?_, ?_, ?_, ?_⟩
          · simp [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce, targetArgsRun, targetPrim]
          · change List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code) [value] [targetValue]
            rw [codeEq]
            exact .cons valueRel .nil
          · simpa [codeEq] using finalStates
          · intro key item lookup
            rw [codeEq]
            exact argsGrowth key item lookup

/-- The executable traversal's ordinary-operation case composes its actual
argument-list simulation. Install and force-thunk remain separate cases. -/
theorem callsFuel_ordinaryOp_invariant_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (op : ClosLang.Op) (args : List ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.op trace op args) initial = some (out, final))
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ target, callsListFuel fuel args initial = some (target, final) →
      ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed args target) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.op trace op args) out := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := run
  exact exprSimFuelInvariant_ordinaryOp fuel g allowed trace op args targetArgs notInstall notForce
    (argsIH targetArgs argsRun)

end Flapjack.Compiler.Backend.ClosCall
