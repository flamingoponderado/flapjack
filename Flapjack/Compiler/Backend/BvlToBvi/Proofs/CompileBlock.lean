import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileLabel

/-! Block-constructor simulation for BVL-to-BVI. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Constructing a block in BVI preserves relocated fields and the target
state. Untagged pending BVI dispatcher correspondence review. -/
theorem doBlockCons_target {C F : Type} (tag : Nat) (values : List Value)
    (relocate : Nat → Nat) (state : BviSem.BviState C F) :
    BviSem.doApp (.blockOp (.cons tag)) (values.map (adjustBv relocate)) state =
      .val (adjustBv relocate (.block tag values), state) := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyBlock, BviSem.fromBvl_toBvl, adjustBv_block]

/-- Block construction satisfies the pass simulation given the operand
simulation. Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_blockCons {C F : Type} (tag : Nat) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) : simulation [.op (.blockOp (.cons tag)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.blockOp (.cons tag)) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
      have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
      simp [compileListSource, compileSingSource, argsCompile, nilRight, compileOp] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      simp [BvlSem.doApp, BvlSem.applyBlock] at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
        argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
          argsCompile related sourceOk envOk installed shape global
      refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
      simp only [mapSimulationResult]
      rw [← List.map_reverse, doBlockCons_target]
      rfl

/-- Boolean negation commutes with relocation and preserves target state.
Untagged pending BVI dispatcher correspondence review. -/
theorem doBoolNot_target {C F : Type} (value : Value) (flag : Bool)
    (relocate : Nat → Nat) (state : BviSem.BviState C F)
    (decoded : BvlSem.asBool value = some flag) :
    BviSem.doApp (.blockOp .boolNot) [adjustBv relocate value] state =
      .val (adjustBv relocate (BvlSem.boolValue (!flag)), state) := by
  have targetBool := asBool_adjustBv relocate value
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyBlock, targetBool, decoded, BviSem.fromBvl_toBvl, adjustBv_bool]

/-- Boolean negation satisfies the pass simulation given its operand
simulation. Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_boolNot {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) : simulation [.op (.blockOp .boolNot) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.blockOp .boolNot) arguments env source middle error argsIH argsRun
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
      | cons value rest =>
        cases rest with
        | cons second tail =>
          simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
          exact (notTypeError run.1.symm).elim
        | nil =>
          cases decoded : BvlSem.asBool value with
          | none =>
            simp [BvlSem.doApp, BvlSem.applyBlock, reversed, decoded] at run
            exact (notTypeError run.1.symm).elim
          | some flag =>
            simp [BvlSem.doApp, BvlSem.applyBlock, reversed, decoded] at run
            rcases run with ⟨rfl, rfl⟩
            obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
              argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                argsCompile related sourceOk envOk installed shape global
            refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
            simp only [mapSimulationResult]
            rw [← List.map_reverse, reversed]
            simp only [List.map_cons, List.map_nil]
            rw [doBoolNot_target value flag newRelocate targetNext decoded]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
