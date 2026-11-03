import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantForce

/-! Direct-call expression simulation under the source state invariant. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem ClosProps SemanticPrimitivesProps

/-- A source direct call can only have a non-type-error result when its
arguments fail: the source state relation requires an empty source code map.
The target then propagates the related argument error. This Lean-side case is
not the complete compiler-oracle or growing-state simulation. -/
theorem exprSimFuelInvariant_call {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (ticks label : Nat) (sourceArgs targetArgs : List ClosLang.Exp)
    (argsIH : ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed sourceArgs targetArgs) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed
      (.call trace ticks label sourceArgs) (.call trace ticks label targetArgs) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf sourceWf states
  have argsEnv := envRelFuel_call_args trace ticks label targetArgs envs
  rw [evaluate, fixClock_evaluate] at run
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
        rw [evaluate, fixClock_evaluate, targetArgsRun]
    | val values =>
      have empty : argsFinal.code = HolFiniteMapExact.empty := argsStates.2.2.2.2.2
      have bad : sourceResult = .err (.abort .typeError) := by
        simpa [argsRun, findCode, empty, HolFiniteMapExact.empty] using congrArg Prod.fst run.symm
      exact False.elim (notType bad)

/-- The executable traversal preserves direct calls and composes their actual
argument-list simulation. -/
theorem callsFuel_call_invariant_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (ticks label : Nat) (args : List ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.call trace ticks label args) initial = some (out, final))
    (argsIH : ∀ target, callsListFuel fuel args initial = some (target, final) →
      ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed args target) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.call trace ticks label args) out := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, next⟩, argsRun, rfl, rfl⟩ := run
  exact exprSimFuelInvariant_call fuel g allowed trace ticks label args targetArgs (argsIH targetArgs argsRun)

end Flapjack.Compiler.Backend.ClosCall
