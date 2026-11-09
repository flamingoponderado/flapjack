import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileBlockObserve

/-! Boolean-test simulation for BVL-to-BVI. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Boolean tests commute with value relocation and preserve the target
state. Untagged pending BVI dispatcher correspondence review. -/
theorem doBoolTest_target {C F : Type} (test : AstHOL.Test) (left right : Value)
    (leftFlag rightFlag : Bool) (relocate : Nat → Nat) (state : BviSem.BviState C F)
    (leftDecoded : BvlSem.asBool left = some leftFlag) (rightDecoded : BvlSem.asBool right = some rightFlag) :
    BviSem.doApp (.blockOp (.boolTest test)) [adjustBv relocate left, adjustBv relocate right] state =
      .val (adjustBv relocate (BvlSem.boolValue (leftFlag == rightFlag)), state) := by
  have leftTarget := asBool_adjustBv relocate left
  have rightTarget := asBool_adjustBv relocate right
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyBlock, leftTarget, rightTarget, leftDecoded, rightDecoded, BviSem.fromBvl_toBvl, adjustBv_bool]

/-- Boolean tests satisfy the pass simulation given the operand simulation.
Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_boolTest {C F : Type} (test : AstHOL.Test) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.blockOp (.boolTest test)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.blockOp (.boolTest test)) arguments env source middle error argsIH argsRun
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
      | cons left tail =>
        cases tail with
        | nil =>
          simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
          exact (notTypeError run.1.symm).elim
        | cons right rest =>
          cases rest with
          | cons third tail =>
            simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
            exact (notTypeError run.1.symm).elim
          | nil =>
            cases leftDecoded : BvlSem.asBool left with
            | none =>
              simp [BvlSem.doApp, BvlSem.applyBlock, reversed, leftDecoded] at run
              exact (notTypeError run.1.symm).elim
            | some leftFlag =>
              cases rightDecoded : BvlSem.asBool right with
              | none =>
                simp [BvlSem.doApp, BvlSem.applyBlock, reversed, leftDecoded, rightDecoded] at run
                exact (notTypeError run.1.symm).elim
              | some rightFlag =>
                simp [BvlSem.doApp, BvlSem.applyBlock, reversed, leftDecoded, rightDecoded] at run
                rcases run with ⟨rfl, rfl⟩
                obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                  argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                    argsCompile related sourceOk envOk installed shape global
                refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
                rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                simp only [mapSimulationResult]
                rw [← List.map_reverse, reversed]
                simp only [List.map_cons, List.map_nil]
                rw [doBoolTest_target test left right leftFlag rightFlag newRelocate targetNext leftDecoded rightDecoded]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
