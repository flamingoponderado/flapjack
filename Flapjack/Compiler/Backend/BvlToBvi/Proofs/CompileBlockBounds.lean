import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileBoolTest

/-! Block bounds checks in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Relocating block elements preserves the result of a bounds check.
Untagged pending BVI dispatcher correspondence review. -/
theorem doBlockBounds_target {C F : Type} (tag : Nat) (fields : List Value)
    (index : Int) (relocate : Nat → Nat) (state : BviSem.BviState C F) :
    BviSem.doApp (.blockOp .boundsCheckBlock)
      [adjustBv relocate (.block tag fields), adjustBv relocate (.number index)] state =
      .val (adjustBv relocate (BvlSem.boolValue (decide (0 ≤ index ∧ index < Int.ofNat fields.length))), state) := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyBlock, BviSem.fromBvl_toBvl, adjustBv_block, adjustBv, adjustBv_bool]

/-- Block bounds checks satisfy pass simulation given the operand simulation.
Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_blockBounds {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.blockOp .boundsCheckBlock) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.blockOp .boundsCheckBlock) arguments env source middle error argsIH argsRun
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
        simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
        exact (notTypeError run.1.symm).elim
      | cons first tail =>
        cases tail with
        | nil =>
          simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
          exact (notTypeError run.1.symm).elim
        | cons second rest =>
          cases rest with
          | cons third tail =>
            simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
            exact (notTypeError run.1.symm).elim
          | nil =>
            cases first with
            | block tag fields =>
              cases second with
              | number index =>
                simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
                rcases run with ⟨rfl, rfl⟩
                obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                  argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                    argsCompile related sourceOk envOk installed shape global
                refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
                rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                simp only [mapSimulationResult]
                rw [← List.map_reverse, reversed]
                simp only [List.map_cons, List.map_nil]
                rw [doBlockBounds_target tag fields index newRelocate targetNext]
                simp
              | _ =>
                all_goals
                  simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
                  exact (notTypeError run.1.symm).elim
            | _ =>
              all_goals
                simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
                exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
