module

public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Simulation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.SemanticsRelated
public import Flapjack.FiniteMap.EmptyExact

@[expose] public section

/-! Whole-program observations of let-operation cleanup. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Initial states satisfy the let-operation relation under the source's
oracle and maximum-application assumptions. This Lean-side helper has no
standalone HOL declaration. -/
theorem initialState_related {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C)
    (auxEmpty : ∀ index, (oracle index).2.2 = []) (positive : 1 ≤ maxApp) :
    StateRel (initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) clock)
      (initialState ffi maxApp HolFiniteMapExact.empty (pureCo compileInc ∘ oracle) compiler clock) := by
  simp [StateRel, initialState, fmapRel, Flapjack.optionRel, HolFiniteMapExact.empty, auxEmpty, positive]

/-- The source traversal preserves whole-program observations under the
original non-failure, oracle and maximum-application hypotheses. This Lean-side
helper has no standalone HOL declaration. -/
theorem semantics_let_op_core {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) (program : List ClosLang.Exp)
    (_notFail : semantics ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) program ≠ .fail)
    (auxEmpty : ∀ index, (oracle index).2.2 = []) (positive : 1 ≤ maxApp) :
    semantics ffi maxApp HolFiniteMapExact.empty (pureCo compileInc ∘ oracle) compiler (compileList program) =
      semantics ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) program := by
  classical
  have simulations : ∀ clock,
      ResultRel
        (evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle
          (pureCc compileInc compiler) clock)).1
        (evaluate (compileList program) [] (initialState ffi maxApp HolFiniteMapExact.empty
          (pureCo compileInc ∘ oracle) compiler clock)).1 ∧
      (evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle
          (pureCc compileInc compiler) clock)).2.ffi =
        (evaluate (compileList program) [] (initialState ffi maxApp HolFiniteMapExact.empty
          (pureCo compileInc ∘ oracle) compiler clock)).2.ffi := by
    intro clock
    cases sourceRun : evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle
        (pureCc compileInc compiler) clock) with
    | mk result final =>
      obtain ⟨targetResult, targetFinal, targetRun, resultRel, stateRel⟩ :=
        SimulationPort.let_op_correct program [] _ result final [] _
          ⟨sourceRun, .nil, initialState_related ffi maxApp clock oracle compiler auxEmpty positive⟩
      simp only [compileSource_eq_list] at targetRun
      change evaluate (compileList program) [] _ = _ at targetRun
      rw [targetRun]
      exact ⟨resultRel, stateRel.2.2.2.2.2.2.1.symm⟩
  apply Eq.symm
  apply semantics_eq_of_related_evaluations
  intro clock
  obtain ⟨results, ffiEq⟩ := simulations clock
  have toStandard (left right : Result (List Value) Value) (h : ResultRel left right) :
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel left right := by
    cases left <;> cases right <;> simp_all [ResultRel, SemanticPrimitivesProps.resultRel]
    case err.err left right =>
      cases left <;> cases right <;> simp_all [SemanticPrimitivesProps.excRel]
  have observed := resultRelOutcome (List.Forall₂ ValueRel) ValueRel _ _ (toStandard _ _ results)
  exact ⟨observed.1, observed.2, ffiEq⟩

/-- Let-operation cleanup preserves the original whole-program semantics. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "semantics_let_op"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem semantics_let_op {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) (program : List ClosLang.Exp)
    (notFail : semantics ffi maxApp Flapjack.HolFiniteMapExact.holEmpty oracle
      (pureCc compileIncSource compiler) program ≠ .fail)
    (assumptions : (∀ index, (oracle index).2.2 = []) ∧ 1 ≤ maxApp) :
    semantics ffi maxApp Flapjack.HolFiniteMapExact.holEmpty (pureCo compileIncSource ∘ oracle) compiler (compileSource program) =
      semantics ffi maxApp Flapjack.HolFiniteMapExact.holEmpty oracle (pureCc compileIncSource compiler) program := by
  simpa [compileIncSource_eq, HolFiniteMapExact.holEmpty] using
    semantics_let_op_core ffi maxApp oracle compiler program (by simpa [compileIncSource_eq, HolFiniteMapExact.holEmpty] using notFail) assumptions.1 assumptions.2

end Flapjack.Compiler.Backend.ClosLetop
