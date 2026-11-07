import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileThunkUpdate

/-! Thunk allocation in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- A well-formed thunk allocation satisfies pass simulation given operand
simulation. Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_allocThunk {C F : Type} (mode : AstHOL.ThunkMode) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.thunkOp (.allocThunk mode)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.thunkOp (.allocThunk mode)) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
      have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
      simp [compileListSource, compileSingSource, argsCompile, nilRight, compileOp] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases reversed : values.reverse with
      | nil =>
        simp [BvlSem.doApp, reversed] at run
        exact (notTypeError run.1.symm).elim
      | cons value rest =>
        cases rest with
        | cons second tail =>
          simp [BvlSem.doApp, reversed] at run
          exact (notTypeError run.1.symm).elim
        | nil =>
          by_cases bad : BvlSem.badThunkUpdate mode value middle.refs
          · simp [BvlSem.doApp, reversed, bad] at run
            exact (notTypeError run.1.symm).elim
          · simp [BvlSem.doApp, reversed, bad] at run
            rcases run with ⟨rfl, rfl⟩
            obtain ⟨targetNext, midRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
              argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                argsCompile related sourceOk envOk installed shape global
            have preserved := evaluateOk arguments env source (.val values) middle argsRun sourceOk envOk
            have growth := BvlProps.evaluateRefsSubset arguments env source middle (.val values) argsRun
            have valueOk : bvOk middle.refs value := by
              apply (bvOkList_iff _ _).1 preserved.2.1 value
              have : value ∈ values.reverse := by simp [reversed]
              simpa using this
            have targetBad : ¬ BvlSem.badThunkUpdate mode (adjustBv midRelocate value) targetNext.refs := by
              simpa [badThunkUpdate_stateRel midRelocate middle targetNext mode value relatedNext valueOk] using bad
            obtain ⟨extended, keyEq, agree, relatedAlloc⟩ :=
              stateRel_allocateFresh midRelocate middle targetNext (BvlSem.leastUnusedRef middle.refs)
                (BvlSem.leastUnusedRef targetNext.refs) (.thunk mode value) relatedNext preserved.1
                (BvlSem.leastUnusedRef_unused middle.refs) (BvlSem.leastUnusedRef_unused targetNext.refs)
            have envChange := adjustMap_eq_of_ok midRelocate extended env middle.refs preserved.2.2 agree
            have valueChange := adjustBv_eq_of_ok midRelocate value extended middle.refs valueOk agree
            have sourceAgree : ∀ key, source.refs.lookup key ≠ none → relocate key = extended key := by
              intro key present
              exact (refsEq key present).trans (agree key (growth key present))
            refine ⟨{ targetNext with refs := targetNext.refs.updateEq (BvlSem.leastUnusedRef targetNext.refs,
                .thunk mode (adjustBv extended value)) }, extended, clock, ?_, ?_, envEq.trans envChange, sourceAgree⟩
            · rw [envChange] at targetArgs
              rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
              simp only [mapSimulationResult]
              rw [← List.map_reverse, reversed]
              simp only [List.map_cons, List.map_nil]
              rw [valueChange] at targetBad
              simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
                BviSem.toBvl, BviSem.fromBvl, valueChange, targetBad, adjustBv, keyEq]
            · simpa [adjustRef] using relatedAlloc

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
