module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Simulation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.SemanticsSimulation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateEventsClockFull
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
  have terminatingEq :
      terminatingObservation ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) program =
      terminatingObservation ffi maxApp HolFiniteMapExact.empty (pureCo compileInc ∘ oracle) compiler (removeList program) := by
    funext behavior
    apply propext
    constructor
    · rintro ⟨clock, result, final, outcome, sourceRun, outcomeEq, behaviorEq⟩
      have notTimeout : result ≠ .err (.abort .timeoutError) := by
        intro impossible
        subst result
        simp at outcomeEq
      cases targetRun : evaluate (removeList program) [] (targetState clock) with
      | mk targetResult targetFinal =>
        obtain ⟨extra, sourceResult, sourceFinal, sourceExtended, related, ffiEq⟩ :=
          simulation clock targetResult targetFinal targetRun
        have shifted := evaluate_initial_addClock ffi maxApp clock extra HolFiniteMapExact.empty oracle
          (pureCc compileInc compiler) program result final sourceRun notTimeout
        change evaluate program [] (sourceState (clock + extra)) = _ at shifted
        rw [sourceExtended] at shifted
        obtain ⟨resultEq, stateEq⟩ := Prod.mk.inj shifted
        subst sourceResult
        refine ⟨clock, targetResult, targetFinal, outcome, targetRun, ?_, ?_⟩
        · exact (resultHasOutcome_iff _ outcome).mp
            (((resultRel_observations _ _ related).2 outcome).mp ((resultHasOutcome_iff _ outcome).mpr outcomeEq))
        · have finalFfi : final.ffi = targetFinal.ffi := by
            rw [← ffiEq, stateEq]
          simpa [finalFfi] using behaviorEq
    · rintro ⟨clock, result, final, outcome, targetRun, outcomeEq, behaviorEq⟩
      obtain ⟨extra, sourceResult, sourceFinal, sourceRun, related, ffiEq⟩ := simulation clock result final targetRun
      refine ⟨clock + extra, sourceResult, sourceFinal, outcome, sourceRun, ?_, ?_⟩
      · exact (resultHasOutcome_iff _ outcome).mp
          (((resultRel_observations _ _ related).2 outcome).mpr ((resultHasOutcome_iff _ outcome).mpr outcomeEq))
      · simpa [ffiEq] using behaviorEq
  have tracesEq :
      HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList
        (evaluate (removeList program) [] (targetState clock)).2.ffi.ioEvents) =
      HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList
        (evaluate program [] (sourceState clock)).2.ffi.ioEvents) := by
    apply clocked_traces_lub_eq
    · exact evaluate_initial_ioEvents_mono ffi maxApp HolFiniteMapExact.empty (pureCo compileInc ∘ oracle) compiler (removeList program)
    · exact evaluate_initial_ioEvents_mono ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) program
    · intro clock
      cases targetRun : evaluate (removeList program) [] (targetState clock) with
      | mk result final =>
        obtain ⟨extra, sourceResult, sourceFinal, sourceRun, _, ffiEq⟩ := simulation clock result final targetRun
        exact ⟨extra, by simp [sourceRun, ffiEq]⟩
  unfold semantics
  simp only [HolFiniteMapExact.holEmpty, show ¬ ∃ clock, (evaluate program [] (initialState ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc compileInc compiler) clock)).1 = .err (.abort .typeError) from
      fun ⟨clock, error⟩ => sourceSafe clock error,
    show ¬ ∃ clock, (evaluate (removeList program) [] (initialState ffi maxApp HolFiniteMapExact.empty
      (pureCo compileInc ∘ oracle) compiler clock)).1 = .err (.abort .typeError) from
      fun ⟨clock, error⟩ => targetSafe clock error, ite_false]
  rw [terminatingEq, ← tracesEq]

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
