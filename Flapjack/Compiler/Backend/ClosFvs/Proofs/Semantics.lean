module

public import Flapjack.Compiler.Backend.ClosFvs.Proofs.Simulation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Semantics
public import Flapjack.FiniteMap.EmptyExact
public import Flapjack.Compiler.Backend.Semantics.ClosProps.ResultObservations

@[expose] public section

/-! Whole-program observations of free-variable removal. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Initial states satisfy the free-variable relation under the source's
oracle and maximum-application assumptions. -/
theorem initialState_related {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C)
    (auxEmpty : ∀ index, (oracle index).2.2 = []) (positive : 1 ≤ maxApp) :
    StateRel (initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) clock)
      (initialState ffi maxApp HolFiniteMapExact.empty (pureCo compileInc ∘ oracle) compiler clock) := by
  simp [StateRel, initialState, optionRel, HolFiniteMapExact.empty, auxEmpty, positive]

/-- The source traversal preserves whole-program observations under the
original non-failure, oracle and maximum-application hypotheses. -/
theorem semantics_compile_core {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) (program : List ClosLang.Exp)
    (notFail : semantics ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) program ≠ .fail)
    (auxEmpty : ∀ index, (oracle index).2.2 = []) (positive : 1 ≤ maxApp) :
    semantics ffi maxApp HolFiniteMapExact.empty (pureCo compileInc ∘ oracle) compiler (compile program) =
      semantics ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) program := by
  classical
  have sourceSafe := (semantics_ne_fail_iff ffi maxApp HolFiniteMapExact.empty oracle
    (pureCc compileInc compiler) program).mp notFail
  have simulations : ∀ clock,
      ResultRel
        (evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle
          (pureCc compileInc compiler) clock)).1
        (evaluate (compile program) [] (initialState ffi maxApp HolFiniteMapExact.empty
          (pureCo compileInc ∘ oracle) compiler clock)).1 ∧
      (evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle
          (pureCc compileInc compiler) clock)).2.ffi =
        (evaluate (compile program) [] (initialState ffi maxApp HolFiniteMapExact.empty
          (pureCo compileInc ∘ oracle) compiler clock)).2.ffi := by
    intro clock
    cases sourceRun : evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle
        (pureCc compileInc compiler) clock) with
    | mk result final =>
      obtain ⟨targetResult, targetFinal, targetRun, resultRel, stateRel⟩ :=
        SimulationPort.remove_fvs_correct program [] _ result final [] _
          ⟨sourceRun, .nil, initialState_related ffi maxApp clock oracle compiler auxEmpty positive⟩
      change evaluate (compile program) [] _ = _ at targetRun
      rw [targetRun]
      exact ⟨resultRel, stateRel.2.2.2.2.2.2.1.symm⟩
  have targetSafe : ∀ clock,
      (evaluate (compile program) [] (initialState ffi maxApp HolFiniteMapExact.empty
        (pureCo compileInc ∘ oracle) compiler clock)).1 ≠ .err (.abort .typeError) := by
    intro clock bad
    exact sourceSafe clock ((resultRel_observations _ _ (simulations clock).1).1.mpr bad)
  have terminatingEq :
      terminatingObservation ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) program =
      terminatingObservation ffi maxApp HolFiniteMapExact.empty (pureCo compileInc ∘ oracle) compiler
        (compile program) := by
    funext behavior
    apply propext
    constructor <;> intro observed
    · obtain ⟨clock, result, final, outcome, run, outcomeEq, behaviorEq⟩ := observed
      have sim := simulations clock
      rw [run] at sim
      refine ⟨clock, _, _, outcome, rfl, ?_, ?_⟩
      · apply (resultHasOutcome_iff _ outcome).mp
        apply ((resultRel_observations _ _ sim.1).2 outcome).mp
        exact (resultHasOutcome_iff result outcome).mpr outcomeEq
      · simpa [← sim.2] using behaviorEq
    · obtain ⟨clock, result, final, outcome, run, outcomeEq, behaviorEq⟩ := observed
      have sim := simulations clock
      rw [run] at sim
      refine ⟨clock, _, _, outcome, rfl, ?_, ?_⟩
      · apply (resultHasOutcome_iff _ outcome).mp
        apply ((resultRel_observations _ _ sim.1).2 outcome).mpr
        exact (resultHasOutcome_iff result outcome).mpr outcomeEq
      · simpa [sim.2] using behaviorEq
  have tracesEq :
      (fun trace => ∃ clock, trace = HolLList.fromList
        (evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle
          (pureCc compileInc compiler) clock)).2.ffi.ioEvents) =
      (fun trace => ∃ clock, trace = HolLList.fromList
        (evaluate (compile program) [] (initialState ffi maxApp HolFiniteMapExact.empty
          (pureCo compileInc ∘ oracle) compiler clock)).2.ffi.ioEvents) := by
    funext trace
    apply propext
    constructor <;> rintro ⟨clock, h⟩ <;> refine ⟨clock, ?_⟩
    · simpa [(simulations clock).2] using h
    · simpa [← (simulations clock).2] using h
  unfold semantics
  simp only [show ¬ ∃ clock, (evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc compileInc compiler) clock)).1 = .err (.abort .typeError) from
        fun ⟨clock, error⟩ => sourceSafe clock error,
    show ¬ ∃ clock, (evaluate (compile program) [] (initialState ffi maxApp HolFiniteMapExact.empty
      (pureCo compileInc ∘ oracle) compiler clock)).1 = .err (.abort .typeError) from
        fun ⟨clock, error⟩ => targetSafe clock error, if_false]
  rw [← terminatingEq, ← tracesEq]

/-- Free-variable removal preserves the original whole-program semantics. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "semantics_compile"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem semantics_compile {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) (program : List ClosLang.Exp)
    (notFail : semantics ffi maxApp Flapjack.HolFiniteMapExact.holEmpty oracle
      (pureCc compileInc compiler) program ≠ .fail)
    (assumptions : (∀ index, (oracle index).2.2 = []) ∧ 1 ≤ maxApp) :
    semantics ffi maxApp Flapjack.HolFiniteMapExact.holEmpty (pureCo compileInc ∘ oracle) compiler (compile program) =
      semantics ffi maxApp Flapjack.HolFiniteMapExact.holEmpty oracle (pureCc compileInc compiler) program :=
  semantics_compile_core ffi maxApp oracle compiler program notFail assumptions.1 assumptions.2

/-- The production bounded-retry list pass has the same observable semantics
as the untransformed source program. -/
theorem semantics_bounded {C F : Type} (ffi : HolFfiState F) (fuel maxApp : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) (program : List ClosLang.Exp)
    (notFail : semantics ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) program ≠ .fail)
    (assumptions : (∀ index, (oracle index).2.2 = []) ∧ 1 ≤ maxApp) :
    ∃ transformed, program.mapM (removeBounded fuel 0) = some transformed ∧
      semantics ffi maxApp HolFiniteMapExact.empty (pureCo compileInc ∘ oracle) compiler transformed =
        semantics ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) program :=
  ⟨compile program, compileBounded_eq_source fuel program,
    semantics_compile_core ffi maxApp oracle compiler program notFail assumptions.1 assumptions.2⟩

end Flapjack.Compiler.Backend.ClosFvs
