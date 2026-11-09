import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileBlock

/-! Pure block observations in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Block operations whose only successful argument is an ordinary block. -/
inductive BlockObservation where
  | tagEq : Nat → BlockObservation
  | lenEq : Nat → BlockObservation
  | tagLenEq : Nat → Nat → BlockObservation
  | length : BlockObservation

/-- The source operation represented by an observation. -/
def BlockObservation.op : BlockObservation → ClosLang.BlockOp
  | .tagEq tag => .tagEq tag
  | .lenEq n => .lenEq n
  | .tagLenEq tag n => .tagLenEq tag n
  | .length => .lengthBlock

/-- The result of observing the tag or size of a block. -/
def BlockObservation.result : BlockObservation → Nat → List Value → Value
  | .tagEq tag, actual, _ => BvlSem.boolValue (actual == tag)
  | .lenEq n, _, fields => BvlSem.boolValue (fields.length == n)
  | .tagLenEq tag n, actual, fields => BvlSem.boolValue (actual == tag && fields.length == n)
  | .length, _, fields => .number fields.length

/-- Relocation preserves block observations. -/
theorem BlockObservation.result_adjust (observation : BlockObservation) (tag : Nat)
    (fields : List Value) (relocate : Nat → Nat) :
    observation.result tag (fields.map (adjustBv relocate)) =
      adjustBv relocate (observation.result tag fields) := by
  cases observation <;> simp [BlockObservation.result, adjustBv, adjustBv_bool]

/-- Observing a relocated block gives the relocated result and leaves the
target state unchanged. Untagged pending BVI dispatcher review. -/
theorem doBlockObservation_target {C F : Type} (observation : BlockObservation)
    (tag : Nat) (fields : List Value) (relocate : Nat → Nat) (state : BviSem.BviState C F) :
    BviSem.doApp (.blockOp observation.op) [adjustBv relocate (.block tag fields)] state =
      .val (adjustBv relocate (observation.result tag fields), state) := by
  cases observation <;> simp [BlockObservation.op, BlockObservation.result, adjustBv_block,
    BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
    BviSem.fromBvl_toBvl, adjustBv, adjustBv_bool]

/-- Pure block observations satisfy the pass simulation given the operand
simulation. Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_blockObservation {C F : Type} (observation : BlockObservation)
    (arguments : List Bvl.Exp) (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.blockOp observation.op) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.blockOp observation.op) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
      have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
      have lowered : compileOp (.blockOp observation.op) argsCode = .op (.blockOp observation.op) argsCode := by
        cases observation <;> simp [BlockObservation.op, compileOp]
      simp [compileListSource, compileSingSource, argsCompile, nilRight, lowered] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases reversed : values.reverse with
      | nil =>
        cases observation <;> simp [BlockObservation.op, BvlSem.doApp, BvlSem.applyBlock, reversed] at run <;>
          exact (notTypeError run.1.symm).elim
      | cons value rest =>
        cases rest with
        | cons second tail =>
          cases observation <;> simp [BlockObservation.op, BvlSem.doApp, BvlSem.applyBlock, reversed] at run <;>
            exact (notTypeError run.1.symm).elim
        | nil =>
          cases value with
          | block tag fields =>
            have sourceRun : (res, next) = ( .val [observation.result tag fields], middle) := by
              cases observation <;> simpa [BlockObservation.op, BlockObservation.result,
                BvlSem.doApp, BvlSem.applyBlock, reversed] using run.symm
            cases sourceRun
            obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
              argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                argsCompile related sourceOk envOk installed shape global
            refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
            simp only [mapSimulationResult]
            rw [← List.map_reverse, reversed]
            simp only [List.map_cons, List.map_nil]
            rw [doBlockObservation_target observation tag fields newRelocate targetNext]
          | _ =>
            all_goals cases observation <;> simp [BlockObservation.op, BvlSem.doApp, BvlSem.applyBlock, reversed] at run <;>
              exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
