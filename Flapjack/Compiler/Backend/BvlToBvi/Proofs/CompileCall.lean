import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileForce

/-! Call case of BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Call simulation from the argument simulation and dynamically selected
body simulations at smaller clocks. Untagged pending BVI evaluator and
dispatcher correspondence review. -/
theorem simulation_call {C F : Type} (ticks : Nat) (dest : Option Nat) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source)
    (bodyIH : ∀ (body : Bvl.Exp) (args : List Value) (s : BvlSem.State (Nat × C) F),
      s.clock < source.clock → simulation [body] args s) :
    simulation [.call ticks dest arguments] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
  have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
  simp [compileListSource, compileSingSource, argsCompile, nilRight] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  have shape : BvlHandle.Proofs.handleOk arguments := by
    simpa [BvlHandle.Proofs.handleOk] using handlers
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult mid =>
    have sourceGrowth := BvlProps.evaluateRefsSubset arguments env source mid argsResult argsRun
    have sourcePreserved := evaluateOk arguments env source argsResult mid argsRun sourceOk envOk
    have sourceClock := BvlSem.evaluate_clock_le arguments env source
    rw [argsRun] at sourceClock
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
    cases argsResult with
    | err error =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨targetNext, newRelocate, clock, targetRun, relatedNext, envEq, refsEq⟩ :=
        argsIH n (.err error) next target finalName argsCode argsAux relocate argsRun notTypeError
          argsCompile related sourceOk envOk installed shape global
      refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
      cases error <;> simp [mapSimulationResult]
    | val values =>
      obtain ⟨targetMid, midRelocate, argsClock, targetArgs, relatedMid, envMidEq, refsMidEq⟩ :=
        argsIH n (.val values) mid target finalName argsCode argsAux relocate argsRun (by simp)
          argsCompile related sourceOk envOk installed shape global
      cases selected : BvlSem.findCode dest values mid.code with
      | none =>
        simp [selected] at run
        exact (notTypeError run.1.symm).elim
      | some pair =>
        rcases pair with ⟨callArgs, body⟩
        obtain ⟨bodyName, converted, bodyAux, bodyFinal, bodyCompiled, targetFind, bodyInstalled, bodyShape⟩ :=
          stateRel_findCode midRelocate mid targetMid dest values callArgs body relatedMid selected
        have clockEq : mid.clock = targetMid.clock := relatedMid.2.2.2.1
        by_cases timeout : mid.clock < ticks + 1
        · have targetTimeout : targetMid.clock < ticks + 1 := by omega
          have resetRel : stateRel midRelocate { mid with clock := 0 } { targetMid with clock := 0 } := by
            have shifted := stateRel_decClock midRelocate mid targetMid relatedMid mid.clock
            simpa [BvlSem.decClock, BviSem.decClock, ← clockEq] using shifted
          simp [selected, timeout] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨{ targetMid with clock := 0 }, midRelocate, argsClock, ?_, resetRel, envMidEq, refsMidEq⟩
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
          simp [mapSimulationResult, targetFind, targetTimeout]
        · have targetAvailable : ¬ targetMid.clock < ticks + 1 := by omega
          have bodyRun : BvlSem.evaluate [body] callArgs (BvlSem.decClock (ticks + 1) mid) = (res, next) := by
            simpa [selected, timeout] using run
          have argsOk : bvOkList mid.refs callArgs :=
            findCode_bvOk dest values callArgs mid.code body mid.refs selected sourcePreserved.2.1
          have relatedDec := stateRel_decClock midRelocate mid targetMid relatedMid (ticks + 1)
          have sourceOkDec : stateOk (BvlSem.decClock (ticks + 1) mid) :=
            (stateOk_decClock (ticks + 1) mid).2 sourcePreserved.1
          have bodyClockSmaller : (BvlSem.decClock (ticks + 1) mid).clock < source.clock := by
            simp only [BvlSem.decClock] at *
            omega
          have targetGlobal := BviProps.evaluate_global_mono argsCode (env.map (adjustBv midRelocate))
            (BviProps.incClock argsClock target) targetMid (.val (values.map (adjustBv midRelocate))) (by
              simpa [mapSimulationResult] using targetArgs) (by simpa [BviProps.incClock] using global)
          obtain ⟨targetFinal, finalRelocate, bodyClock, targetBody, relatedFinal, callArgsEq, refsFinalEq⟩ :=
            bodyIH body callArgs (BvlSem.decClock (ticks + 1) mid) bodyClockSmaller bodyName res next
              (BviSem.decClock (ticks + 1) targetMid) bodyFinal [converted] bodyAux midRelocate bodyRun notTypeError
              bodyCompiled relatedDec sourceOkDec argsOk bodyInstalled bodyShape targetGlobal
          have envFinalEq := adjustMap_eq_of_ok midRelocate finalRelocate env mid.refs sourcePreserved.2.2 refsFinalEq
          have valuesEq := adjustMap_eq_of_ok midRelocate finalRelocate values mid.refs sourcePreserved.2.1 refsFinalEq
          have shiftedArgs := BviProps.evaluate_inv_clock argsCode (env.map (adjustBv midRelocate))
            (BviProps.incClock argsClock target) targetMid (.val (values.map (adjustBv midRelocate))) bodyClock
            (by simpa [mapSimulationResult] using targetArgs) (by simp)
          rw [BviProps.incClock_add, envFinalEq, valuesEq] at shiftedArgs
          have targetFindFinal : BvlSem.findCode
              (dest.map (fun loc => bvlNumStubs + bvlToBviNamespaces * loc))
              (values.map (adjustBv finalRelocate)) targetMid.code =
                some (callArgs.map (adjustBv finalRelocate), BviLet.compileSing [] 0 converted) := by
            simpa [← valuesEq, ← callArgsEq] using targetFind
          have mappedOk : mapSimulationResult finalRelocate res ≠ .err (.abort .typeError) := by
            cases res with
            | val values => simp [mapSimulationResult]
            | err error => cases error <;> simp_all [mapSimulationResult]
          have optimized := BviLet.Proofs.evaluate_compileList [converted] (callArgs.map (adjustBv finalRelocate))
            (BviProps.incClock bodyClock (BviSem.decClock (ticks + 1) targetMid)) targetFinal
            (mapSimulationResult finalRelocate res) targetBody mappedOk
          have optimizedRun : BviSem.evaluate [BviLet.compileSing [] 0 converted]
              (callArgs.map (adjustBv finalRelocate)) (BviProps.incClock bodyClock (BviSem.decClock (ticks + 1) targetMid)) =
                (mapSimulationResult finalRelocate res, targetFinal) := by
            simpa [BviLet.compileList, BviSem.evaluateTuple] using optimized
          have refsEq : ∀ key, source.refs.lookup key ≠ none → relocate key = finalRelocate key := by
            intro key present
            exact (refsMidEq key present).trans (refsFinalEq key (sourceGrowth key present))
          refine ⟨targetFinal, finalRelocate, bodyClock + argsClock, ?_, relatedFinal,
            envMidEq.trans envFinalEq, refsEq⟩
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, shiftedArgs]
          simp only
          have mappedFind : BvlSem.findCode
              (dest.map (fun loc => bvlNumStubs + bvlToBviNamespaces * loc))
              (values.map (adjustBv finalRelocate)) (BviProps.incClock bodyClock targetMid).code =
                some (callArgs.map (adjustBv finalRelocate), BviLet.compileSing [] 0 converted) := by
            simpa [BviProps.incClock] using targetFindFinal
          rw [mappedFind]
          have available : ¬ (BviProps.incClock bodyClock targetMid).clock < ticks + 1 := by
            simp only [BviProps.incClock]
            omega
          simp only [available, ↓reduceIte, BviProps.decClock_incClock targetMid ticks bodyClock targetAvailable]
          rw [BviSem.fixClock_evaluate, optimizedRun]
          cases res with
          | val values => simp [mapSimulationResult]
          | err error => cases error <;> simp [mapSimulationResult]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
