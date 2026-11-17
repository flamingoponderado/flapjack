module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Simulation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.SemanticsRelated
public import Flapjack.FiniteMap.EmptyExact
public import Flapjack.Compiler.Backend.Semantics.ClosProps.ResultObservations

@[expose] public section

/-! Whole-program observations of closure tick removal. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Initial states satisfy the tick-removal relation under the original
oracle and maximum-application assumptions. This is Flapjack infrastructure
for the observational theorem. -/
theorem initialState_related {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C)
    (auxEmpty : ∀ index, (oracle index).2.2 = []) (positive : 1 ≤ maxApp) :
    StateRel (initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) clock)
      (initialState ffi maxApp HolFiniteMapExact.empty (pureCo compileInc ∘ oracle) compiler clock) := by
  simp [StateRel, initialState, Flapjack.optionRel, HolFiniteMapExact.empty, auxEmpty, positive]

/-- Tick removal preserves the original whole-program observations. -/
theorem semantics_remove_ticks_core {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) (program : List ClosLang.Exp)
    (notFail : semantics ffi maxApp HolFiniteMapExact.holEmpty oracle (pureCc compileInc compiler) program ≠ .fail)
    (assumptions : (∀ index, (oracle index).2.2 = []) ∧ 1 ≤ maxApp) :
    semantics ffi maxApp HolFiniteMapExact.holEmpty oracle (pureCc compileInc compiler) program =
      semantics ffi maxApp HolFiniteMapExact.holEmpty (pureCo compileInc ∘ oracle) compiler (removeList program) := by
  classical
  let sourceState := fun clock => initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) clock
  let targetState := fun clock => initialState ffi maxApp HolFiniteMapExact.empty (pureCo compileInc ∘ oracle) compiler clock
  have sourceSafe : ∀ clock, (evaluate program [] (sourceState clock)).1 ≠ .err (.abort .typeError) :=
    (semantics_ne_fail_iff ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) program).mp notFail
  have simulation : ∀ clock result final,
      evaluate (removeList program) [] (targetState clock) = (result, final) →
      ∃ extra sourceResult sourceFinal,
        evaluate program [] (sourceState (clock + extra)) = (sourceResult, sourceFinal) ∧
        ResultRel sourceResult result ∧ sourceFinal.ffi = final.ffi := by
    intro clock result final run
    obtain ⟨extra, sourceResult, sourceFinal, sourceRun, resultRel, stateRel⟩ :=
      SimulationPort.remove_ticks_correct program [] (targetState clock) result final [] (sourceState clock)
        ⟨by simpa using run, .nil, initialState_related ffi maxApp clock oracle compiler assumptions.1 assumptions.2⟩
    refine ⟨extra, sourceResult, sourceFinal, ?_, resultRel, stateRel.2.2.2.2.2.2.1.symm⟩
    simpa [sourceState, initialState] using sourceRun
  have targetSafe : ∀ clock, (evaluate (removeList program) [] (targetState clock)).1 ≠ .err (.abort .typeError) := by
    intro clock bad
    cases targetRun : evaluate (removeList program) [] (targetState clock) with
    | mk result final =>
      have resultEq : result = .err (.abort .typeError) := by simpa [targetRun] using bad
      obtain ⟨extra, sourceResult, sourceFinal, sourceRun, related, _⟩ := simulation clock result final targetRun
      have sourceError : sourceResult = .err (.abort .typeError) :=
        (resultRel_observations _ _ related).1.mpr resultEq
      exact sourceSafe (clock + extra) (by simpa [sourceRun] using sourceError)
  apply Eq.symm
  apply semantics_eq_of_related_clocked_simulation ffi maxApp
    HolFiniteMapExact.empty HolFiniteMapExact.empty
    (pureCo compileInc ∘ oracle) oracle compiler (pureCc compileInc compiler)
    (removeList program) program targetSafe
  intro clock result final run
  obtain ⟨extra, sourceResult, sourceFinal, sourceRun, related, ffiEq⟩ := simulation clock result final run
  have toStandard (left right : Result (List Value) Value) (h : ResultRel left right) :
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel left right := by
    cases left <;> cases right <;> simp_all [ResultRel, SemanticPrimitivesProps.resultRel]
    case err.err left right =>
      cases left <;> cases right <;> simp_all [SemanticPrimitivesProps.excRel]
  have observed := resultRelOutcome (List.Forall₂ ValueRel) ValueRel _ _ (toStandard _ _ related)
  exact ⟨extra, sourceResult, sourceFinal, sourceRun, observed.1.symm, observed.2.symm, ffiEq.symm⟩

/-- Tick removal preserves the original whole-program observations. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "semantics_remove_ticks"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem semantics_remove_ticks {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) (program : List ClosLang.Exp)
    (notFail : semantics ffi maxApp HolFiniteMapExact.holEmpty oracle (pureCc compileIncSource compiler) program ≠ .fail)
    (assumptions : (∀ index, (oracle index).2.2 = []) ∧ 1 ≤ maxApp) :
    semantics ffi maxApp HolFiniteMapExact.holEmpty oracle (pureCc compileIncSource compiler) program =
      semantics ffi maxApp HolFiniteMapExact.holEmpty (pureCo compileIncSource ∘ oracle) compiler (removeSource program) := by
  simpa [compileIncSource_eq] using
    semantics_remove_ticks_core ffi maxApp oracle compiler program (by simpa [compileIncSource_eq] using notFail) assumptions

end Flapjack.Compiler.Backend.ClosTicks
