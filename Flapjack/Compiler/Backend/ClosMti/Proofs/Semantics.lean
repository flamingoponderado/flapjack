module

public import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateMutual
public import Flapjack.Compiler.Backend.Semantics.ClosSem.SemanticsRelated
public import Flapjack.FiniteMap.EmptyExact

@[expose] public section

/-! Observable consequences for the current Lean closure evaluator. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem BackendProps SemanticPrimitivesProps

/-- Initial states are related when the source oracle satisfies the unary and
empty-label invariant. This is Lean-side infrastructure pending HOL review. -/
theorem initialStates_related {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C)
    (positive : 1 ≤ maxApp)
    (safe : ∀ n, (oracle n).2.2 = [] ∧ ∀ e ∈ (oracle n).2.1, ClosProps.noMti e) :
    StateRel
      (initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc (compileInc maxApp) compiler) clock)
      (initialState ffi maxApp HolFiniteMapExact.empty (pureCo (compileInc maxApp) ∘ oracle) compiler clock) := by
  refine ⟨safe, rfl, rfl, rfl, positive, rfl, rfl, .nil, ?_, rfl, rfl⟩
  constructor
  · intro key
    simp [initialState, HolFiniteMapExact.empty]
  · intro key value found
    simp [initialState, HolFiniteMapExact.empty] at found

/-- Multi-argument introduction preserves observable semantics under the
original non-failure, oracle, application-limit, and unary assumptions. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "semantics_intro_multi"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem semantics_intro_multi {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) (program : List ClosLang.Exp)
    (_notFail : semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (pureCc (compileInc maxApp) compiler) program ≠ .fail)
    (invariants : (∀ n, (oracle n).2.2 = [] ∧ ∀ e ∈ (oracle n).2.1, ClosProps.noMti e) ∧
      1 ≤ maxApp ∧ ∀ e ∈ program, ClosProps.noMti e) :
    semantics ffi maxApp HolFiniteMapExact.holEmpty (pureCo (compileInc maxApp) ∘ oracle) compiler
        (introList maxApp program) =
      semantics ffi maxApp HolFiniteMapExact.holEmpty oracle (pureCc (compileInc maxApp) compiler) program := by
  obtain ⟨safe, positive, unary⟩ := invariants
  apply Eq.symm
  change semantics ffi maxApp HolFiniteMapExact.empty oracle (pureCc (compileInc maxApp) compiler) program =
    semantics ffi maxApp HolFiniteMapExact.empty (pureCo (compileInc maxApp) ∘ oracle) compiler
      (introList maxApp program)
  apply semantics_eq_of_related_evaluations
  intro clock
  let source := initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc (compileInc maxApp) compiler) clock
  let target := initialState ffi maxApp HolFiniteMapExact.empty (pureCo (compileInc maxApp) ∘ oracle) compiler clock
  have states : StateRel source target := initialStates_related ffi maxApp clock oracle compiler positive safe
  cases sourceRun : evaluate program [] source with
  | mk sourceResult sourceFinal =>
    obtain ⟨targetResult, targetFinal, targetRun, resultsRelated, finalStates⟩ :=
      intro_multi_correct program [] source sourceResult sourceFinal [] () target ⟨sourceRun, unary, .nil, states⟩
    change resultOutcome sourceResult = resultOutcome (evaluate (introList maxApp program) [] target).1 ∧
      (sourceResult = .err (.abort .typeError) ↔
        (evaluate (introList maxApp program) [] target).1 = .err (.abort .typeError)) ∧
      sourceFinal.ffi = (evaluate (introList maxApp program) [] target).2.ffi
    have targetRun' : evaluate (introList maxApp program) [] target = (targetResult, targetFinal) := by
      simpa [source, initialState] using targetRun
    rw [targetRun']
    have observed := resultRelOutcome (List.Forall₂ (ValueRel maxApp)) (ValueRel maxApp)
      sourceResult targetResult (by simpa [source, initialState] using resultsRelated)
    exact ⟨observed.1, observed.2, finalStates.2.2.2.2.2.2.1.symm⟩

/-- The optional multi-argument pass preserves the original observable
semantics under the HOL non-failure, compiler, oracle, and unary assumptions. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "semantics_compile"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem semantics_compile {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (oracle : CompileOracle C) (compiler1 : Compiler C) (program : List ClosLang.Exp)
    (enabled : Bool) (compiler : Compiler C) (oracle1 : CompileOracle C)
    (premises : semantics ffi maxApp HolFiniteMapExact.holEmpty oracle compiler1 program ≠ .fail ∧
      compiler1 = (if enabled then pureCc (compileInc maxApp) else id) compiler ∧
      oracle1 = (if enabled then pureCo (compileInc maxApp) else id) ∘ oracle ∧
      (enabled = true → (∀ n, (oracle n).2.2 = [] ∧ ∀ e ∈ (oracle n).2.1, ClosProps.noMti e) ∧
        1 ≤ maxApp ∧ ∀ e ∈ program, ClosProps.noMti e)) :
    semantics ffi maxApp HolFiniteMapExact.holEmpty oracle1 compiler (compile enabled maxApp program) =
      semantics ffi maxApp HolFiniteMapExact.holEmpty oracle compiler1 program := by
  obtain ⟨notFail, compilerEq, oracleEq, enabledSafe⟩ := premises
  subst compiler1
  subst oracle1
  cases enabled with
  | false => simp [compile]
  | true =>
    obtain ⟨safe, positive, unary⟩ := enabledSafe rfl
    simpa [compile] using
      semantics_intro_multi ffi maxApp oracle compiler program notFail ⟨safe, positive, unary⟩

end Flapjack.Compiler.Backend.ClosMti
