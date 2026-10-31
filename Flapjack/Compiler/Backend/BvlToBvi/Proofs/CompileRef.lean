import Flapjack.Compiler.Backend.BvlToBvi.Proofs.RefRelocate

/-! Reference-array allocation in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Reference-array allocation executes at the least free target address.
Untagged pending BVI dispatcher correspondence review. -/
theorem doRef_target {C F : Type} (values : List Value) (target : BviSem.BviState C F) :
    BviSem.doApp (.memOp .ref) values target =
      .val (.refPtr true (BvlSem.leastUnusedRef target.refs),
        { target with refs := target.refs.updateEq (BvlSem.leastUnusedRef target.refs, .valueArray values) }) := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl]

/-- Reference-array allocation satisfies pass simulation given the operand
simulation. Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_ref {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp .ref) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.memOp .ref) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
      have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
      simp [compileListSource, compileSingSource, argsCompile, nilRight, compileOp] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      simp [BvlSem.doApp, BvlSem.applyMemory] at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨targetNext, midRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
        argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
          argsCompile related sourceOk envOk installed shape global
      have preserved := evaluateOk arguments env source (.val values) middle argsRun sourceOk envOk
      have growth := BvlProps.evaluateRefsSubset arguments env source middle (.val values) argsRun
      obtain ⟨extended, keyEq, agree, relatedAlloc⟩ :=
        stateRel_allocateFresh midRelocate middle targetNext (BvlSem.leastUnusedRef middle.refs)
          (BvlSem.leastUnusedRef targetNext.refs) (.valueArray values.reverse) relatedNext preserved.1
          (BvlSem.leastUnusedRef_unused middle.refs) (BvlSem.leastUnusedRef_unused targetNext.refs)
      have envChange := adjustMap_eq_of_ok midRelocate extended env middle.refs preserved.2.2 agree
      have valuesOk : bvOkList middle.refs values.reverse := by
        apply (bvOkList_iff _ _).2
        intro item member
        exact (bvOkList_iff _ _).1 preserved.2.1 item (by simpa using member)
      have valuesChange := adjustMap_eq_of_ok midRelocate extended values.reverse middle.refs valuesOk agree
      have sourceAgree : ∀ key, source.refs.lookup key ≠ none → relocate key = extended key := by
        intro key present
        exact (refsEq key present).trans (agree key (growth key present))
      refine ⟨{ targetNext with refs := targetNext.refs.updateEq (BvlSem.leastUnusedRef targetNext.refs,
          .valueArray (values.reverse.map (adjustBv extended))) },
        extended, clock, ?_, ?_, envEq.trans envChange, sourceAgree⟩
      · rw [envChange] at targetArgs
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
        simp only [mapSimulationResult]
        rw [← List.map_reverse, valuesChange]
        rw [doRef_target]
        simp [adjustBv, keyEq]
      · simpa [adjustRef] using relatedAlloc

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
