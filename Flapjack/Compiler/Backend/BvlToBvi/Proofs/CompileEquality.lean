import Flapjack.Compiler.Backend.BvlToBvi.Proofs.EqualityRel

/-! Equality operations in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- A successful equality test is preserved by relocation. Untagged pending
BVI dispatcher correspondence review. -/
theorem doEquality_target {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (left right : Value) (result : Bool) (related : stateRel relocate source target)
    (leftOk : bvOk source.refs left) (rightOk : bvOk source.refs right)
    (equal : BvlSem.doEq source.refs left right = .val result) :
    BviSem.doApp (.blockOp .equal) [adjustBv relocate left, adjustBv relocate right] target =
      .val (adjustBv relocate (BvlSem.boolValue result), target) := by
  have eqRel := doEq_relocate relocate source.refs target.refs left right related.1 leftOk rightOk
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
    BviSem.toBvl, BviSem.fromBvl, adjustBv_bool, eqRel, equal]

/-- Equality satisfies pass simulation given operand simulation. Untagged
pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_equal {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.blockOp .equal) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.blockOp .equal) arguments env source middle error argsIH argsRun
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
            cases equal : BvlSem.doEq middle.refs left right with
            | typeError =>
              simp [BvlSem.doApp, BvlSem.applyBlock, reversed, equal] at run
              exact (notTypeError run.1.symm).elim
            | val result =>
              simp [BvlSem.doApp, BvlSem.applyBlock, reversed, equal] at run
              rcases run with ⟨rfl, rfl⟩
              obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                  argsCompile related sourceOk envOk installed shape global
              have preserved := evaluateOk arguments env source (.val values) middle argsRun sourceOk envOk
              have leftOk : bvOk middle.refs left := by
                apply (bvOkList_iff _ _).1 preserved.2.1 left
                have : left ∈ values.reverse := by simp [reversed]
                simpa using this
              have rightOk : bvOk middle.refs right := by
                apply (bvOkList_iff _ _).1 preserved.2.1 right
                have : right ∈ values.reverse := by simp [reversed]
                simpa using this
              refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
              rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
              simp only [mapSimulationResult]
              rw [← List.map_reverse, reversed]
              simp only [List.map_cons, List.map_nil]
              rw [doEquality_target newRelocate middle targetNext left right result relatedNext leftOk rightOk equal]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
