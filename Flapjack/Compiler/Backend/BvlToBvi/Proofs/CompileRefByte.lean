import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileRefArray

/-! Replicated byte-array allocation in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- The target allocates a replicated byte array at its least free address.
Untagged pending BVI dispatcher correspondence review. -/
theorem doRefByte_target {C F : Type} (count byte : Int) (byteValue : BitVec 8)
    (target : BviSem.BviState C F) (nonnegative : ¬ count < 0)
    (decoded : ClosSem.intToByte byte = some byteValue) :
    BviSem.doApp (.memOp (.refByte false)) [.number count, .number byte] target =
      .val (.refPtr true (BvlSem.leastUnusedRef target.refs),
        { target with refs := target.refs.updateEq (BvlSem.leastUnusedRef target.refs,
          .byteArray false (List.replicate count.toNat byteValue)) }) := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, nonnegative, decoded]

/-- Replicated byte-array allocation satisfies pass simulation given operand
simulation. Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_refByte {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp (.refByte false)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.memOp (.refByte false)) arguments env source middle error argsIH argsRun
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
        simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run
        exact (notTypeError run.1.symm).elim
      | cons first tail =>
        cases tail with
        | nil =>
          simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run
          exact (notTypeError run.1.symm).elim
        | cons value rest =>
          cases rest with
          | cons third tail =>
            simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run
            exact (notTypeError run.1.symm).elim
          | nil =>
            cases value with
            | number byte =>
              cases first with
              | number count =>
                by_cases negative : count < 0
                · simp [BvlSem.doApp, BvlSem.applyMemory, reversed, negative] at run
                  exact (notTypeError run.1.symm).elim
                · cases decoded : ClosSem.intToByte byte with
                  | none =>
                    simp [BvlSem.doApp, BvlSem.applyMemory, reversed, negative, decoded] at run
                    exact (notTypeError run.1.symm).elim
                  | some byteValue =>
                    simp [BvlSem.doApp, BvlSem.applyMemory, reversed, negative, decoded] at run
                    rcases run with ⟨rfl, rfl⟩
                    obtain ⟨targetNext, midRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                      argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                        argsCompile related sourceOk envOk installed shape global
                    have preserved := evaluateOk arguments env source (.val values) middle argsRun sourceOk envOk
                    have growth := BvlProps.evaluateRefsSubset arguments env source middle (.val values) argsRun
                    obtain ⟨extended, keyEq, agree, relatedAlloc⟩ :=
                      stateRel_allocateFresh midRelocate middle targetNext (BvlSem.leastUnusedRef middle.refs)
                        (BvlSem.leastUnusedRef targetNext.refs) (.byteArray false (List.replicate count.toNat byteValue))
                        relatedNext preserved.1 (BvlSem.leastUnusedRef_unused middle.refs)
                        (BvlSem.leastUnusedRef_unused targetNext.refs)
                    have envChange := adjustMap_eq_of_ok midRelocate extended env middle.refs preserved.2.2 agree
                    have sourceAgree : ∀ key, source.refs.lookup key ≠ none → relocate key = extended key := by
                      intro key present
                      exact (refsEq key present).trans (agree key (growth key present))
                    refine ⟨{ targetNext with refs := targetNext.refs.updateEq (BvlSem.leastUnusedRef targetNext.refs,
                        .byteArray false (List.replicate count.toNat byteValue)) },
                      extended, clock, ?_, ?_, envEq.trans envChange, sourceAgree⟩
                    · rw [envChange] at targetArgs
                      rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                      simp only [mapSimulationResult]
                      rw [← List.map_reverse, reversed]
                      simp only [List.map_cons, List.map_nil, adjustBv]
                      rw [doRefByte_target count byte byteValue targetNext negative decoded]
                      simp [keyEq]
                    · simpa [adjustRef] using relatedAlloc
              | _ =>
                all_goals
                  simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run
                  exact (notTypeError run.1.symm).elim

            | _ =>
              all_goals
                cases first <;> simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run <;>
                  exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
