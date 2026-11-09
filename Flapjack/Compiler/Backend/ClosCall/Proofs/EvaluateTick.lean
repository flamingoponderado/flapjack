module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateVariable

@[expose] public section

/-! Structural evaluation cases for direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- A related environment remains related when compiler state, permitted
locations, and the target code map grow. -/
theorem envRelFuel_mono {fuel : Nat} {g g' : State} {allowed allowed' : Set Nat}
    {code code' : HolFiniteMapExact Nat (Nat × ClosLang.Exp)}
    {sourceEnv targetEnv : List ClosSem.Value} {offset : Nat}
    {fns : List (Nat × ClosLang.Exp)}
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv offset fns)
    (stateGrowth : stateExtends g g') (allowedGrowth : allowed ⊆ allowed')
    (codeGrowth : ∀ key value, code.lookup key = some value → code'.lookup key = some value) :
    EnvRelFuel fuel g' allowed' code' sourceEnv targetEnv offset fns := by
  apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
  apply envRel_mono _ ((envRelFuel_iff _ _ _ _ _ _ _ _).mp related)
  intro _ _ ⟨_, _, values⟩
  exact valueRelFuel_mono values stateGrowth allowedGrowth codeGrowth

/-- Source-driven simulation for one expression, using the fuel-aware value
and state relations. This local induction interface does not yet cover the
compiler-oracle and growing-state obligations of HOL's full theorem. -/
def ExprSimFuel {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (sourceExp targetExp : ClosLang.Exp) : Prop :=
  ∀ (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value)
    (sourceFinal : ClosSem.State (NumSet × C) F),
    evaluate [sourceExp] sourceEnv source = (sourceResult, sourceFinal) →
    sourceResult ≠ .err (.abort .typeError) →
    EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, targetExp)] →
    StateRelFuel fuel g allowed source target →
    ∃ targetResult targetFinal,
      evaluate [targetExp] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, target.code.lookup key = some value →
        targetFinal.code.lookup key = some value)

/-- Variables satisfy the single-expression simulation. -/
theorem exprSimFuel_var {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (index : Nat) :
    ExprSimFuel (C := C) (F := F) fuel g allowed (.var trace index) (.var trace index) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs states
  obtain ⟨targetResult, targetFinal, targetRun, results, finalStates⟩ :=
    evaluate_var_fuel fuel g allowed trace index sourceEnv targetEnv source target
      sourceResult sourceFinal run notType envs states
  have targetSame : targetFinal = target := by
    cases lookup : targetEnv[index]? <;> simp_all [evaluate]
  subst targetFinal
  exact ⟨targetResult, target, targetRun, results, finalStates, fun _ _ h => h⟩

/-- Synchronized clock subtraction preserves the state relation. -/
theorem stateRelFuel_decClock {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {source : ClosSem.State (NumSet × C) F} {target : ClosSem.State C F}
    (states : StateRelFuel fuel g allowed source target) (amount : Nat) :
    StateRelFuel fuel g allowed (decClock amount source) (decClock amount target) := by
  obtain ⟨ffi, clock, maxApp, globals, refs, sourceCode⟩ := states
  exact ⟨ffi, by simp [decClock, clock], maxApp, globals, refs, sourceCode⟩

/-- Clamping related final clocks by equal starting clocks preserves the
state relation, independently of the two evaluation results. -/
theorem stateRelFuel_fixClock {C F A B : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    (sourceStart : ClosSem.State (NumSet × C) F) (targetStart : ClosSem.State C F)
    (sourceResult : A) (targetResult : B)
    {sourceFinal : ClosSem.State (NumSet × C) F} {targetFinal : ClosSem.State C F}
    (startClocks : sourceStart.clock = targetStart.clock)
    (states : StateRelFuel fuel g allowed sourceFinal targetFinal) :
    StateRelFuel fuel g allowed (fixClock sourceStart (sourceResult, sourceFinal)).2
      (fixClock targetStart (targetResult, targetFinal)).2 := by
  obtain ⟨ffi, clock, maxApp, globals, refs, sourceCode⟩ := states
  exact ⟨ffi, by simp [fixClock, startClocks, clock], maxApp, globals, refs, sourceCode⟩

/-- Matching ticks simulate by the induction hypothesis for their bodies. -/
theorem exprSimFuel_tick {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (sourceBody targetBody : ClosLang.Exp)
    (bodyIH : ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody) :
    ExprSimFuel (C := C) (F := F) fuel g allowed (.tick trace sourceBody) (.tick trace targetBody) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs states
  have clocks := states.2.1
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by omega
    have sourceEq : sourceResult = .err (.abort .timeoutError) ∧ sourceFinal = source := by
      simpa [evaluate, zero] using run.symm
    obtain ⟨rfl, rfl⟩ := sourceEq
    refine ⟨.err (.abort .timeoutError), target, ?_, ?_, states, fun _ _ h => h⟩
    · simp [evaluate, targetZero]
    · rfl
  · have targetNonzero : target.clock ≠ 0 := by omega
    have bodyRun : evaluate [sourceBody] sourceEnv (decClock 1 source) = (sourceResult, sourceFinal) := by
      simpa [evaluate, zero] using run
    have bodyEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)] := by
      apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
      have h := (envRelFuel_iff fuel g allowed target.code sourceEnv targetEnv 0
        [(0, .tick trace targetBody)]).mp envs
      simpa [envRel, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] using h
    obtain ⟨targetResult, targetFinal, targetRun, results, finalStates, codeGrowth⟩ :=
      bodyIH sourceEnv targetEnv (decClock 1 source) (decClock 1 target)
        sourceResult sourceFinal bodyRun notType bodyEnv (stateRelFuel_decClock states 1)
    refine ⟨targetResult, targetFinal, ?_, results, finalStates, codeGrowth⟩
    simpa [evaluate, targetNonzero] using targetRun

end Flapjack.Compiler.Backend.ClosCall
